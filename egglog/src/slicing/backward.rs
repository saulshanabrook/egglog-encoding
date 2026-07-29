//! Backward dynamic slicing from recorded criteria.
//!
//! A slice selects one sound historical support cone. It does not claim global
//! minimality and does not construct a proof.

use std::collections::VecDeque;

use crate::core_relations::{
    AppliedEqualityId, CauseRef, Criterion, CriterionEndpointOccurrence, EdgeHorizon,
    EqualityEndpoint, EqualityReason, FactCellRef, FactId, FiringEqualitySource, FiringId,
    HistoryPosition, ProjectedAppliedEquality, RawAliasWindow, RawCause, RawEqualityEndpoint,
    RawEqualitySupport, ReplayTableKind, ReplayTermId, SourceRef, TableId, TraceView,
    TraceViewError, TypedCellEquality, Value,
};
use crate::numeric_id::NumericId;
use crate::util::{HashMap, HashSet};

use crate::EGraph;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Slice {
    pub(crate) checks: HashSet<u32>,
    pub(crate) facts: HashSet<FactId>,
    pub(crate) firings: HashSet<FiringId>,
    pub(crate) equalities: HashSet<AppliedEqualityId>,
    pub(crate) replay_facts: HashSet<FactId>,
    pub(crate) replay_equalities: HashSet<AppliedEqualityId>,
    pub(crate) replay_removals: HashSet<usize>,
    pub(crate) rekeys: HashSet<HistoryPosition>,
    pub(crate) causes: HashSet<CauseRef>,
    pub(crate) sources: HashSet<SourceRef>,
    pub(crate) firing_terms: HashMap<FiringId, Box<[ReplayTermId]>>,
    /// Occurrence-local availability, key-readiness, and producer-liveness
    /// windows for every call in a firing binding's structural `let-check`
    /// recipe. Aliases may be captured before a selected deletion and then
    /// reused by later grounded waves.
    pub(crate) firing_term_windows: HashMap<FiringId, Box<[Box<[RawAliasWindow]>]>>,
    pub(crate) equality_records: HashMap<AppliedEqualityId, ProjectedAppliedEquality>,
    denotation_equalities: HashSet<AppliedEqualityId>,
    requirements: Vec<RawEqualitySupport>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ReplayOwner {
    Firing(FiringId),
    Source(SourceRef),
}

#[derive(Clone, Debug, Default)]
struct OwnerEffects {
    facts: Vec<FactId>,
    equalities: Vec<AppliedEqualityId>,
    removals: Vec<usize>,
}

type OwnerIndex = HashMap<ReplayOwner, OwnerEffects>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum KeyCell {
    Base(Value),
    Equality(EqualityEndpoint),
}

#[derive(Default)]
struct SelectedEqualityDsu {
    parent: HashMap<EqualityEndpoint, EqualityEndpoint>,
}

impl SelectedEqualityDsu {
    fn find(&mut self, term: EqualityEndpoint) -> EqualityEndpoint {
        let parent = *self.parent.entry(term).or_insert(term);
        if parent == term {
            return term;
        }
        let root = self.find(parent);
        self.parent.insert(term, root);
        root
    }

    fn union(&mut self, left: EqualityEndpoint, right: EqualityEndpoint) -> bool {
        let left = self.find(left);
        let right = self.find(right);
        if left == right {
            return false;
        }
        self.parent.insert(right, left);
        true
    }

    fn equivalent(&mut self, left: KeyCell, right: KeyCell) -> bool {
        match (left, right) {
            (KeyCell::Base(left), KeyCell::Base(right)) => left == right,
            (KeyCell::Equality(left), KeyCell::Equality(right)) => {
                left.sort == right.sort && self.find(left) == self.find(right)
            }
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum SliceError {
    #[error(transparent)]
    Trace(#[from] TraceViewError),
    #[error("causal slicing requires the concrete main bridge backend")]
    UnsupportedBackend,
    #[error("causal slicing cannot use a poisoned capture: {0}")]
    Poisoned(String),
    #[error("selected causal support is missing {kind} {id}")]
    MissingSupport { kind: &'static str, id: u64 },
}

impl Slice {
    pub(crate) fn validate_exact_support(&self) -> Result<(), SliceError> {
        for requirement in &self.requirements {
            for id in &requirement.applied {
                if !self.equalities.contains(id) {
                    return Err(SliceError::MissingSupport {
                        kind: "applied equality",
                        id: id.get(),
                    });
                }
            }
            for id in &requirement.facts {
                if !self.facts.contains(id) {
                    return Err(SliceError::MissingSupport {
                        kind: "fact",
                        id: id.get(),
                    });
                }
            }
            for position in &requirement.rekeys {
                if !self.rekeys.contains(position) {
                    return Err(SliceError::MissingSupport {
                        kind: "rekey",
                        id: position.get(),
                    });
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum Work {
    Fact(FactId),
    Firing(FiringId),
    Cause(CauseRef),
    Equality(AppliedEqualityId),
    EqualityDenotation(AppliedEqualityId),
    Rekey(HistoryPosition),
}

fn enqueue_support(slice: &mut Slice, work: &mut VecDeque<Work>, support: RawEqualitySupport) {
    for id in &support.applied {
        work.push_back(Work::Equality(*id));
    }
    for id in &support.facts {
        work.push_back(Work::Fact(*id));
    }
    for position in &support.rekeys {
        work.push_back(Work::Rekey(*position));
    }
    slice.requirements.push(support);
}

fn check_occurrence_cell(occurrence: CriterionEndpointOccurrence) -> Option<FactCellRef> {
    match occurrence {
        CriterionEndpointOccurrence::FactCell(cell) => Some(cell),
        CriterionEndpointOccurrence::Current => None,
    }
}

fn explain_rule_equality(
    view: &mut TraceView<'_>,
    left: FiringEqualitySource,
    right: FiringEqualitySource,
    premises: &[FactId],
    as_of_edges: EdgeHorizon,
    position: HistoryPosition,
) -> Result<RawEqualitySupport, TraceViewError> {
    let premise_cell =
        |source: FiringEqualitySource| -> Result<Option<FactCellRef>, TraceViewError> {
            let FiringEqualitySource::Premise(occurrence) = source else {
                return Ok(None);
            };
            let fact = *premises.get(occurrence.premise).ok_or_else(|| {
                TraceViewError::Invalid(format!(
                    "equality obligation cites missing premise {}",
                    occurrence.premise
                ))
            })?;
            let column = occurrence.column.try_into().map_err(|_| {
                TraceViewError::Invalid("premise occurrence column exceeds u32".into())
            })?;
            Ok(Some(FactCellRef {
                fact,
                column: crate::core_relations::ColumnId::new(column),
            }))
        };
    let left_cell = premise_cell(left)?;
    let right_cell = premise_cell(right)?;
    match (left_cell, right_cell) {
        (Some(left), Some(right)) => {
            return view.explain_fact_cell_support_at(left, right, as_of_edges, position);
        }
        (Some(fact), None) => {
            let FiringEqualitySource::Constant(endpoint) = right else {
                unreachable!("non-premise equality source is always a constant")
            };
            return view.explain_fact_endpoint_support_at(fact, endpoint, as_of_edges, position);
        }
        (None, Some(fact)) => {
            let FiringEqualitySource::Constant(endpoint) = left else {
                unreachable!("non-premise equality source is always a constant")
            };
            return view.explain_fact_endpoint_support_at(fact, endpoint, as_of_edges, position);
        }
        (None, None) => {}
    }

    let mut facts = Vec::new();
    let mut rekeys = Vec::new();
    let mut resolve = |source| -> Result<EqualityEndpoint, TraceViewError> {
        match source {
            FiringEqualitySource::Premise(occurrence) => {
                let fact = *premises.get(occurrence.premise).ok_or_else(|| {
                    TraceViewError::Invalid(format!(
                        "equality obligation cites missing premise {}",
                        occurrence.premise
                    ))
                })?;
                let column = occurrence.column.try_into().map_err(|_| {
                    TraceViewError::Invalid("premise occurrence column exceeds u32".into())
                })?;
                let cell = view.fact_cell_at(
                    FactCellRef {
                        fact,
                        column: crate::core_relations::ColumnId::new(column),
                    },
                    position,
                )?;
                facts.push(fact);
                rekeys.extend(cell.rekeys);
                Ok(cell.created)
            }
            FiringEqualitySource::Constant(endpoint) => Ok(endpoint),
        }
    };
    let left = resolve(left)?;
    let right = resolve(right)?;
    let support = view.explain_equality_support_at(left, right, as_of_edges, position)?;
    facts.extend(support.facts);
    facts.sort_unstable();
    facts.dedup();
    rekeys.extend(support.rekeys);
    rekeys.sort_unstable();
    rekeys.dedup();
    Ok(RawEqualitySupport {
        applied: support.applied,
        facts: facts.into_boxed_slice(),
        rekeys: rekeys.into_boxed_slice(),
    })
}

fn replay_owner_for_cause(
    view: &TraceView<'_>,
    cause: CauseRef,
    memo: &mut HashMap<CauseRef, Option<ReplayOwner>>,
    active: &mut HashSet<CauseRef>,
) -> Result<Option<ReplayOwner>, TraceViewError> {
    if let Some(owner) = memo.get(&cause) {
        return Ok(owner.clone());
    }
    if !active.insert(cause) {
        return Err(TraceViewError::Invalid(format!(
            "trace cause cycle reaches {cause:?}"
        )));
    }
    let owner = match cause {
        CauseRef::Rule(rule) => Some(ReplayOwner::Firing(rule)),
        CauseRef::Cause(id) => match view.cause(id)? {
            RawCause::Source(source) => Some(ReplayOwner::Source(source.clone())),
            RawCause::Merge { incoming, .. } => {
                replay_owner_for_cause(view, incoming, memo, active)?
            }
            RawCause::Rebuild { .. }
            | RawCause::ContainerCanonicalize { .. }
            | RawCause::ContainerRefresh { .. } => None,
        },
    };
    active.remove(&cause);
    memo.insert(cause, owner.clone());
    Ok(owner)
}

fn build_owner_index(view: &TraceView<'_>) -> Result<OwnerIndex, TraceViewError> {
    let totals = view.totals();
    let mut index = OwnerIndex::default();
    let mut memo = HashMap::default();
    let mut active = HashSet::default();
    for raw in 1..=totals.facts {
        let fact = FactId::new(raw);
        let cause = view.fact(fact)?.cause;
        if let Some(owner) = replay_owner_for_cause(view, cause, &mut memo, &mut active)? {
            index.entry(owner).or_default().facts.push(fact);
        }
    }
    for raw in 1..=totals.applied_equalities {
        let equality = AppliedEqualityId::new(raw);
        let event = view.applied_equality(equality)?;
        let owner = match event.reason {
            EqualityReason::RuleUnion(rule) => Some(ReplayOwner::Firing(rule)),
            EqualityReason::SourceUnion { cause }
            | EqualityReason::MergeFn { cause }
            | EqualityReason::Congruence { cause, .. } => {
                replay_owner_for_cause(view, CauseRef::Cause(cause), &mut memo, &mut active)?
            }
        };
        if let Some(owner) = owner {
            index.entry(owner).or_default().equalities.push(equality);
        }
    }
    for removal in 0..totals.removals as usize {
        let owner = ReplayOwner::Firing(view.removal(removal)?.cause);
        index.entry(owner).or_default().removals.push(removal);
    }
    Ok(index)
}

fn mark_replay_equality(
    view: &mut TraceView<'_>,
    slice: &mut Slice,
    work: &mut VecDeque<Work>,
    id: AppliedEqualityId,
) -> Result<(), TraceViewError> {
    if slice.replay_equalities.insert(id) {
        let event = view.project_applied_equality(id)?;
        slice.equality_records.insert(id, event);
        work.push_back(Work::EqualityDenotation(id));
    }
    Ok(())
}

fn mark_owner_visible(
    view: &mut TraceView<'_>,
    index: &OwnerIndex,
    slice: &mut Slice,
    work: &mut VecDeque<Work>,
    owner: &ReplayOwner,
) -> Result<(), TraceViewError> {
    let Some(effects) = index.get(owner) else {
        return Ok(());
    };
    slice.replay_facts.extend(effects.facts.iter().copied());
    for id in effects.equalities.iter().copied() {
        mark_replay_equality(view, slice, work, id)?;
    }
    slice
        .replay_removals
        .extend(effects.removals.iter().copied());
    Ok(())
}

fn selected_equality_dsu(slice: &Slice) -> SelectedEqualityDsu {
    let mut dsu = SelectedEqualityDsu::default();
    for id in &slice.replay_equalities {
        let event = &slice.equality_records[id];
        dsu.union(event.left, event.right);
    }
    dsu
}

fn equality_landmark_is_replay_visible(
    view: &mut TraceView<'_>,
    slice: &Slice,
    as_of_edges: EdgeHorizon,
    position: HistoryPosition,
    equalities: &[TypedCellEquality],
) -> Result<bool, TraceViewError> {
    for pair in equalities {
        let support = view.explain_raw_equality_support_at(
            RawEqualityEndpoint {
                sort: pair.left.sort,
                raw: pair.left.raw,
            },
            RawEqualityEndpoint {
                sort: pair.right.sort,
                raw: pair.right.raw,
            },
            as_of_edges,
            position,
        )?;
        if support
            .applied
            .iter()
            .any(|edge| !slice.replay_equalities.contains(edge))
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn maintenance_cause_is_replay_visible(
    view: &mut TraceView<'_>,
    slice: &Slice,
    cause: CauseRef,
    current_event: AppliedEqualityId,
    active: &mut HashSet<CauseRef>,
) -> Result<bool, TraceViewError> {
    if !active.insert(cause) {
        return Err(TraceViewError::Invalid(format!(
            "trace cause cycle reaches {cause:?}"
        )));
    }
    let visible = match cause {
        CauseRef::Rule(rule) => slice.firings.contains(&rule),
        CauseRef::Cause(id) => match view.cause(id)? {
            RawCause::Source(source) => slice.sources.contains(source),
            RawCause::Merge {
                incoming,
                prior_fact,
            } => {
                let incoming = maintenance_cause_is_replay_visible(
                    view,
                    slice,
                    incoming,
                    current_event,
                    active,
                )?;
                let prior = slice.replay_facts.contains(&prior_fact);
                incoming && prior
            }
            RawCause::Rebuild {
                prior_fact,
                as_of_edges,
                position,
                equalities,
                ..
            }
            | RawCause::ContainerRefresh {
                prior_fact,
                as_of_edges,
                position,
                equalities,
                ..
            } => {
                if as_of_edges.get() >= current_event.get() {
                    return Err(TraceViewError::Invalid(format!(
                        "maintenance equality {current_event:?} depends on non-earlier equality cutoff {as_of_edges:?}"
                    )));
                }
                slice.replay_facts.contains(&prior_fact)
                    && equality_landmark_is_replay_visible(
                        view,
                        slice,
                        as_of_edges,
                        position,
                        equalities,
                    )?
            }
            RawCause::ContainerCanonicalize {
                as_of_edges,
                position,
                equalities,
                ..
            } => {
                if as_of_edges.get() >= current_event.get() {
                    return Err(TraceViewError::Invalid(format!(
                        "maintenance equality {current_event:?} depends on non-earlier equality cutoff {as_of_edges:?}"
                    )));
                }
                equality_landmark_is_replay_visible(view, slice, as_of_edges, position, equalities)?
            }
        },
    };
    active.remove(&cause);
    Ok(visible)
}

fn select_replay_maintenance_equalities(
    view: &mut TraceView<'_>,
    slice: &mut Slice,
    work: &mut VecDeque<Work>,
) -> Result<bool, TraceViewError> {
    if view.totals().removals == 0 {
        return Ok(false);
    }
    let mut selected_any = false;
    let mut active = HashSet::default();
    // AppliedEqualityIds are allocated in execution order. Every maintenance
    // landmark is cut off before the equality event that cites it, so all of
    // its equality prerequisites have already been decided when this scan
    // reaches the event. Owner-selected equalities are seeded before this
    // pass. Consequently one chronological pass is both sufficient and
    // necessary; a fixpoint would turn a dense event log into quadratic work.
    for raw in 1..=view.totals().applied_equalities {
        let id = AppliedEqualityId::new(raw);
        if slice.replay_equalities.contains(&id) {
            continue;
        }
        let event = view.applied_equality(id)?;
        let cause = match event.reason {
            EqualityReason::RuleUnion(_) | EqualityReason::SourceUnion { .. } => continue,
            EqualityReason::MergeFn { cause } | EqualityReason::Congruence { cause, .. } => {
                CauseRef::Cause(cause)
            }
        };
        debug_assert!(active.is_empty());
        if !maintenance_cause_is_replay_visible(view, slice, cause, id, &mut active)? {
            continue;
        }
        mark_replay_equality(view, slice, work, id)?;
        selected_any = true;
    }
    Ok(selected_any)
}

fn replay_key_at(
    view: &mut TraceView<'_>,
    fact: FactId,
    position: HistoryPosition,
) -> Result<(TableId, Box<[KeyCell]>), TraceViewError> {
    let record = view.fact(fact)?;
    let table = record.table;
    let values = record.values.to_vec();
    let schema = view.table_schema(table)?;
    let mut key = Vec::with_capacity(schema.key_columns);
    for column in 0..schema.key_columns {
        if schema.columns[column].is_some() {
            let column_id = crate::core_relations::ColumnId::new(
                column
                    .try_into()
                    .map_err(|_| TraceViewError::Invalid("table key column exceeds u32".into()))?,
            );
            let endpoint = view
                .fact_cell_at(
                    FactCellRef {
                        fact,
                        column: column_id,
                    },
                    position,
                )?
                .endpoint;
            key.push(KeyCell::Equality(endpoint));
        } else {
            let value = values.get(column).copied().ok_or_else(|| {
                TraceViewError::Invalid(format!("fact {fact:?} has no key column {column}"))
            })?;
            key.push(KeyCell::Base(value));
        }
    }
    Ok((table, key.into_boxed_slice()))
}

fn position_before_event(position: HistoryPosition) -> Result<HistoryPosition, TraceViewError> {
    position
        .get()
        .checked_sub(1)
        .map(HistoryPosition::new)
        .ok_or_else(|| {
            TraceViewError::Invalid("causal event has no preceding history position".into())
        })
}

fn keys_equivalent(dsu: &mut SelectedEqualityDsu, left: &[KeyCell], right: &[KeyCell]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .copied()
            .zip(right.iter().copied())
            .all(|(left, right)| dsu.equivalent(left, right))
}

fn select_interfering_removals(
    view: &mut TraceView<'_>,
    slice: &mut Slice,
    work: &mut VecDeque<Work>,
) -> Result<bool, TraceViewError> {
    let mut dsu = selected_equality_dsu(slice);
    let replay_facts = slice.replay_facts.iter().copied().collect::<Vec<_>>();
    let mut selected_any = false;
    for index in 0..view.totals().removals as usize {
        if slice.replay_removals.contains(&index) {
            continue;
        }
        let removal = view.removal(index)?.clone();
        if !slice.replay_facts.contains(&removal.removed_fact) {
            continue;
        }
        let removed_record = view.fact(removal.removed_fact)?;
        let schema = view.table_schema(removed_record.table)?;
        if schema.kind == ReplayTableKind::PresenceRelation {
            continue;
        }
        let victim_position = position_before_event(removal.position)?;
        let (table, victim_key) = replay_key_at(view, removal.removed_fact, victim_position)?;
        let mut interferes = false;
        for later in replay_facts.iter().copied() {
            let record = view.fact(later)?;
            if record.table != table || record.position <= removal.position {
                continue;
            }
            let (_, later_key) = replay_key_at(view, later, record.position)?;
            if keys_equivalent(&mut dsu, &victim_key, &later_key) {
                interferes = true;
                break;
            }
        }
        if interferes {
            slice.replay_removals.insert(index);
            work.push_back(Work::Firing(removal.cause));
            selected_any = true;
        }
    }
    Ok(selected_any)
}

fn seed_check_root(
    view: &mut TraceView<'_>,
    slice: &mut Slice,
    work: &mut VecDeque<Work>,
    root: &Criterion,
) -> Result<(), TraceViewError> {
    slice.checks.insert(root.check);
    work.extend(root.premises.iter().copied().map(Work::Fact));

    for ((left_endpoint, right_endpoint), (left_occurrence, right_occurrence)) in root
        .equalities
        .iter()
        .copied()
        .zip(root.equality_occurrences.iter().copied())
    {
        let left_cell = check_occurrence_cell(left_occurrence);
        let right_cell = check_occurrence_cell(right_occurrence);
        let support = match (left_cell, right_cell) {
            (Some(left), Some(right)) => {
                let exact = view.explain_fact_cell_support_at(
                    left,
                    right,
                    root.as_of_edges,
                    root.position,
                )?;
                enqueue_support(slice, work, exact);
                let left_source = view.explain_fact_endpoint_availability_at(
                    left,
                    left_endpoint,
                    root.as_of_edges,
                    root.position,
                )?;
                enqueue_support(slice, work, left_source.support);
                view.explain_fact_endpoint_availability_at(
                    right,
                    right_endpoint,
                    root.as_of_edges,
                    root.position,
                )?
                .support
            }
            (Some(fact), None) => {
                let source = view.explain_fact_endpoint_availability_at(
                    fact,
                    left_endpoint,
                    root.as_of_edges,
                    root.position,
                )?;
                enqueue_support(slice, work, source.support);
                view.explain_fact_endpoint_support_at(
                    fact,
                    right_endpoint,
                    root.as_of_edges,
                    root.position,
                )?
            }
            (None, Some(fact)) => {
                let source = view.explain_fact_endpoint_availability_at(
                    fact,
                    right_endpoint,
                    root.as_of_edges,
                    root.position,
                )?;
                enqueue_support(slice, work, source.support);
                view.explain_fact_endpoint_support_at(
                    fact,
                    left_endpoint,
                    root.as_of_edges,
                    root.position,
                )?
            }
            (None, None) => view.explain_equality_support_at(
                left_endpoint,
                right_endpoint,
                root.as_of_edges,
                root.position,
            )?,
        };
        enqueue_support(slice, work, support);
    }
    Ok(())
}

fn slice_roots(view: &mut TraceView<'_>, roots: Vec<Criterion>) -> Result<Slice, TraceViewError> {
    let owner_index = build_owner_index(view)?;
    let mut slice = Slice::default();
    let mut work = VecDeque::new();
    for root in &roots {
        seed_check_root(view, &mut slice, &mut work, root)?;
    }

    loop {
        while let Some(item) = work.pop_front() {
            match item {
                Work::Fact(id) => {
                    if !slice.facts.insert(id) {
                        continue;
                    }
                    slice.replay_facts.insert(id);
                    let cause = view.fact(id)?.cause;
                    work.push_back(Work::Cause(cause));
                }
                Work::Firing(id) => {
                    if !slice.firings.insert(id) {
                        continue;
                    }
                    mark_owner_visible(
                        view,
                        &owner_index,
                        &mut slice,
                        &mut work,
                        &ReplayOwner::Firing(id),
                    )?;
                    let firing = view.firing(id)?;
                    let rule = firing.rule;
                    let position = firing.position;
                    let as_of_edges = firing.as_of_edges;
                    let premises = firing.premises.to_vec();
                    let merge_reads = firing.merge_reads.to_vec();
                    work.extend(premises.iter().copied().map(Work::Fact));
                    work.extend(merge_reads.into_iter().map(Work::Fact));
                    let terms = view.firing_terms(id)?;
                    let mut windows = Vec::with_capacity(terms.len());
                    for binding in 0..terms.len() {
                        let availability = view.explain_firing_term_availability(id, binding)?;
                        windows.push(availability.aliases);
                        enqueue_support(&mut slice, &mut work, availability.support);
                    }
                    slice.firing_terms.insert(id, terms);
                    slice
                        .firing_term_windows
                        .insert(id, windows.into_boxed_slice());
                    for (left, right) in view.rule_equality_layout(rule)?.iter().copied() {
                        let support = explain_rule_equality(
                            view,
                            left,
                            right,
                            &premises,
                            as_of_edges,
                            position,
                        )?;
                        enqueue_support(&mut slice, &mut work, support);
                    }
                }
                Work::Cause(cause) => {
                    if !slice.causes.insert(cause) {
                        continue;
                    }
                    let CauseRef::Cause(id) = cause else {
                        let CauseRef::Rule(id) = cause else {
                            unreachable!()
                        };
                        work.push_back(Work::Firing(id));
                        continue;
                    };
                    match view.cause(id)? {
                        RawCause::Source(source) => {
                            let source = source.clone();
                            slice.sources.insert(source.clone());
                            mark_owner_visible(
                                view,
                                &owner_index,
                                &mut slice,
                                &mut work,
                                &ReplayOwner::Source(source),
                            )?;
                        }
                        RawCause::Rebuild {
                            prior_fact,
                            as_of_edges,
                            position,
                            equalities,
                            ..
                        }
                        | RawCause::ContainerRefresh {
                            prior_fact,
                            as_of_edges,
                            position,
                            equalities,
                            ..
                        } => {
                            let pairs = equalities.to_vec();
                            work.push_back(Work::Fact(prior_fact));
                            for pair in pairs {
                                let support = view.explain_raw_equality_support_at(
                                    RawEqualityEndpoint {
                                        sort: pair.left.sort,
                                        raw: pair.left.raw,
                                    },
                                    RawEqualityEndpoint {
                                        sort: pair.right.sort,
                                        raw: pair.right.raw,
                                    },
                                    as_of_edges,
                                    position,
                                )?;
                                enqueue_support(&mut slice, &mut work, support);
                            }
                        }
                        RawCause::ContainerCanonicalize {
                            as_of_edges,
                            position,
                            equalities,
                            ..
                        } => {
                            let pairs = equalities.to_vec();
                            for pair in pairs {
                                let support = view.explain_raw_equality_support_at(
                                    RawEqualityEndpoint {
                                        sort: pair.left.sort,
                                        raw: pair.left.raw,
                                    },
                                    RawEqualityEndpoint {
                                        sort: pair.right.sort,
                                        raw: pair.right.raw,
                                    },
                                    as_of_edges,
                                    position,
                                )?;
                                enqueue_support(&mut slice, &mut work, support);
                            }
                        }
                        RawCause::Merge {
                            incoming,
                            prior_fact,
                        } => {
                            work.push_back(Work::Cause(incoming));
                            work.push_back(Work::Fact(prior_fact));
                        }
                    }
                }
                Work::Equality(id) => {
                    if !slice.equalities.insert(id) {
                        continue;
                    }
                    mark_replay_equality(view, &mut slice, &mut work, id)?;
                    let event = slice
                        .equality_records
                        .get(&id)
                        .expect("selected equality lost its projected record")
                        .clone();
                    let reason = event.reason.clone();
                    if let EqualityReason::Congruence {
                        as_of_edges,
                        position,
                        ..
                    } = reason
                    {
                        let support = view.explain_congruence_child_support_at(
                            event.left,
                            event.right,
                            as_of_edges,
                            position,
                        )?;
                        enqueue_support(&mut slice, &mut work, support);
                    }
                    work.push_back(Work::Cause(match reason {
                        EqualityReason::RuleUnion(rule) => CauseRef::Rule(rule),
                        EqualityReason::SourceUnion { cause }
                        | EqualityReason::MergeFn { cause }
                        | EqualityReason::Congruence { cause, .. } => CauseRef::Cause(cause),
                    }));
                }
                Work::EqualityDenotation(id) => {
                    if !slice.denotation_equalities.insert(id) {
                        continue;
                    }
                    let support = view.explain_equality_denotation_before(id)?;
                    enqueue_support(&mut slice, &mut work, support);
                }
                Work::Rekey(position) => {
                    if !slice.rekeys.insert(position) {
                        continue;
                    }
                    let rekey = view.rekey_at(position)?;
                    let fact = rekey.fact;
                    let as_of_edges = rekey.as_of_edges;
                    let equality_position = rekey.equality_position;
                    let outcome = rekey.outcome;
                    let pairs = rekey.equalities.to_vec();
                    work.push_back(Work::Fact(fact));
                    match outcome {
                        crate::core_relations::RekeyOutcome::Moved => {}
                        crate::core_relations::RekeyOutcome::Absorbed(successor)
                        | crate::core_relations::RekeyOutcome::Replaced(successor) => {
                            work.push_back(Work::Fact(successor));
                        }
                    }
                    for pair in pairs {
                        let support = view.explain_raw_equality_support_at(
                            RawEqualityEndpoint {
                                sort: pair.left.sort,
                                raw: pair.left.raw,
                            },
                            RawEqualityEndpoint {
                                sort: pair.right.sort,
                                raw: pair.right.raw,
                            },
                            as_of_edges,
                            equality_position,
                        )?;
                        enqueue_support(&mut slice, &mut work, support);
                    }
                }
            }
        }
        select_replay_maintenance_equalities(view, &mut slice, &mut work)?;
        let selected_removal = select_interfering_removals(view, &mut slice, &mut work)?;
        if work.is_empty() && !selected_removal {
            break;
        }
    }
    slice
        .validate_exact_support()
        .map_err(|error| TraceViewError::Invalid(error.to_string()))?;
    Ok(slice)
}

#[cfg(test)]
fn slice_view(view: &mut TraceView<'_>, check: u32) -> Result<Slice, TraceViewError> {
    slice_roots(view, vec![view.check_root(check)?.clone()])
}

fn slice_all_view(view: &mut TraceView<'_>) -> Result<Slice, TraceViewError> {
    let roots = view.check_roots().into_iter().cloned().collect();
    slice_roots(view, roots)
}

#[cfg(test)]
pub(crate) fn slice_check(egraph: &EGraph, check: u32) -> Result<Slice, SliceError> {
    egraph
        .capture_catalog
        .as_ref()
        .ok_or(SliceError::UnsupportedBackend)?
        .ensure_healthy()
        .map_err(|error| SliceError::Poisoned(error.to_string()))?;
    let bridge = egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .ok_or(SliceError::UnsupportedBackend)?;
    bridge
        .with_trace_view(|view| slice_view(view, check))
        .map_err(SliceError::Trace)
}

pub(crate) fn slice_all_checks(egraph: &EGraph) -> Result<Slice, SliceError> {
    egraph
        .capture_catalog
        .as_ref()
        .ok_or(SliceError::UnsupportedBackend)?
        .ensure_healthy()
        .map_err(|error| SliceError::Poisoned(error.to_string()))?;
    let bridge = egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .ok_or(SliceError::UnsupportedBackend)?;
    bridge
        .with_trace_view(slice_all_view)
        .map_err(SliceError::Trace)
}

#[cfg(test)]
mod tests {
    use std::sync::OnceLock;

    use super::*;

    fn serial_trace_pool() -> &'static rayon::ThreadPool {
        static SERIAL_POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
        SERIAL_POOL.get_or_init(|| {
            rayon::ThreadPoolBuilder::new()
                .num_threads(1)
                .build()
                .unwrap()
        })
    }

    #[test]
    fn repeated_variable_slice_keeps_exact_equality_support() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64) (B i64) (D i64))
                 (relation R (E))
                 (relation S (E))
                 (relation Out (Unit))
                 (relation Noise (E))
                 (relation Dead (Unit))
                 (rule () ((union (A 1) (B 2))) :name \"eq-ab\")
                 (rule ((R x) (S x)) ((Out ())) :name \"join\")
                 (rule ((Noise x)) ((Dead ())) :name \"dead\")
                 (R (A 1))
                 (S (B 2))
                 (Noise (D 3))
                 (run 2)
                 (check (Out ()))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.firings.len(), 2);
        assert_eq!(slice.equalities.len(), 1);
        assert_eq!(slice.sources.len(), 2);
        assert!(slice.firings.iter().all(|firing| {
            let record = slice.firing_terms.get(firing).unwrap();
            record.len() <= 1
        }));

        let mut damaged = slice.clone();
        damaged.equalities.clear();
        assert!(matches!(
            damaged.validate_exact_support(),
            Err(SliceError::MissingSupport {
                kind: "applied equality",
                ..
            })
        ));
    }

    #[test]
    fn interfering_same_wave_delete_retains_its_independent_firing() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(function f (i64) i64 :merge (max old new))
                 (relation Trigger (Unit))
                 (relation Write (Unit))
                 (relation Done (Unit))
                 (relation Before (i64))
                 (relation After (i64))
                 (set (f 1) 5)
                 (Trigger ())
                 (Write ())
                 (rule ((= value (f 1))) ((Before value)) :name \"observe-before\")
                 (rule ((Trigger u)) ((delete (f 1))) :name \"delete-f\")
                 (rule ((Write u)) ((set (f 1) 2) (Done ())) :name \"rewrite-f\")
                 (rule ((Done u) (= value (f 1))) ((After value)) :name \"observe-after\")
                 (run 2)
                 (check (Before 5) (After 2))",
            )
            .unwrap();

        let bridge = egraph
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        bridge
            .with_trace_view(|view| {
                assert_eq!(view.totals().removals, 1);
                Ok(())
            })
            .unwrap();
        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(
            slice.firings.len(),
            4,
            "the independent delete must be rooted"
        );
        assert_eq!(slice.checks.len(), 1);
        assert!(slice.equalities.is_empty());
        assert!(slice.replay_equalities.is_empty());
        assert_eq!(slice.replay_removals.len(), 1);
    }

    #[test]
    fn all_checks_union_disjoint_cones() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation A (Unit))
                 (relation B (Unit))
                 (relation OutA (Unit))
                 (relation OutB (Unit))
                 (A ())
                 (B ())
                 (rule ((A u)) ((OutA ())) :name \"make-a\")
                 (rule ((B u)) ((OutB ())) :name \"make-b\")
                 (run 1)
                 (check (OutA ()))
                 (check (OutB ()))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        assert_eq!(slice.checks, HashSet::from_iter([0, 1]));
        assert_eq!(slice.firings.len(), 2);
    }

    #[test]
    fn future_selected_child_union_requires_maintenance_congruence_for_interference() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (X) (Y) (F E) (Parent E))
                 (function tag (E) i64 :no-merge)
                 (relation Delete (Unit))
                 (relation Recreate (Unit))
                 (relation Created (E))
                 (relation Before (i64))
                 (relation Out (Unit))
                 (set (tag (Parent (F (X)))) 1)
                 (Delete ())
                 (rule ((= value (tag (Parent (F (X))))))
                       ((Before value))
                       :name \"observe-before\")
                 (rule ((Delete u))
                       ((delete (Parent (F (X)))))
                       :name \"delete-parent\")
                 (run 1)
                 (Recreate ())
                 (rule ((Recreate u))
                       ((set (tag (Parent (F (Y)))) 2)
                        (Created (Parent (F (Y)))))
                       :name \"recreate-parent\")
                 (run 1)
                 (rule ((Created p))
                       ((union (X) (Y)) (Out ()))
                       :name \"merge-children\")
                 (run 1)
                 (check (Before 1) (Out ()))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        assert_eq!(
            slice.replay_removals.len(),
            1,
            "the selected X=Y event automatically makes F(X)=F(Y), so omitting the Parent delete makes replay congruence-collide the stale and recreated rows"
        );

        let mut omitted_creator = EGraph::default();
        serial_trace_pool()
            .install(|| omitted_creator.enable_trace())
            .unwrap();
        omitted_creator
            .parse_and_run_program(
                None,
                "(datatype E (X) (Y) (F E) (Parent E))
                 (function tag (E) i64 :no-merge)
                 (relation Delete (Unit))
                 (relation Recreate (Unit))
                 (relation Created (E))
                 (relation Out (Unit))
                 (set (tag (Parent (F (X)))) 1)
                 (Delete ())
                 (rule ((Delete u))
                       ((delete (Parent (F (X)))))
                       :name \"delete-parent\")
                 (run 1)
                 (Recreate ())
                 (rule ((Recreate u))
                       ((set (tag (Parent (F (Y)))) 2)
                        (Created (Parent (F (Y)))))
                       :name \"recreate-parent\")
                 (run 1)
                 (rule ((Created p))
                       ((union (X) (Y)) (Out ()))
                       :name \"merge-children\")
                 (run 1)
                 (check (Out ()))",
            )
            .unwrap();
        let omitted_slice = slice_all_checks(&omitted_creator).unwrap();
        assert!(
            omitted_slice.replay_removals.is_empty(),
            "when the stale constructor source is absent from replay, its delete is correctly unnecessary"
        );
    }

    #[test]
    fn selected_child_delete_prevents_spurious_parent_delete_interference() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (Leaf i64) (Parent E))
                 (relation DeleteLeaf (Unit))
                 (relation DeleteParent (Unit))
                 (relation Recreate (Unit))
                 (relation Before (E))
                 (relation After (E))
                 (Before (Parent (Leaf 1)))
                 (DeleteLeaf ())
                 (DeleteParent ())
                 (rule ((DeleteLeaf u))
                       ((delete (Leaf 1)))
                       :name \"delete-leaf\")
                 (rule ((DeleteParent u))
                       ((delete (Parent (Leaf 1))))
                       :name \"delete-parent\")
                 (run 1)
                 (Recreate ())
                 (rule ((Recreate u))
                       ((After (Parent (Leaf 1))))
                       :name \"recreate\")
                 (run 1)
                 (check (Before old) (After new))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        assert_eq!(
            slice.replay_removals.len(),
            1,
            "the required Leaf delete prevents old/new Leaf outputs from congruence-colliding, so Parent deletion is noninterfering"
        );
        assert_eq!(
            slice.firings.len(),
            2,
            "only recreate and the required Leaf delete should replay"
        );
    }

    #[test]
    fn same_syntax_constructor_recreation_retains_raw_reconciliation() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (Leaf i64))
                 (relation Delete (i64))
                 (relation Recreate (i64))
                 (relation Before (E))
                 (relation After (E))
                 (ruleset cleanup)
                 (ruleset recreate)
                 (ruleset reconcile)
                 (rule ((Delete key)) ((delete (Leaf key)))
                       :ruleset cleanup :name \"delete-leaf\")
                 (rule ((Recreate key)) ((After (Leaf key)))
                       :ruleset recreate :name \"recreate-leaf\")
                 (rule ((Before old) (After new)) ((union old new))
                       :ruleset reconcile :name \"reconcile\")
                 (Before (Leaf 1))
                 (Delete 1)
                 (Recreate 1)
                 (run cleanup 1)
                 (run recreate 1)
                 (run reconcile 1)
                 (check (Before x) (After x))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        assert_eq!(slice.replay_removals.len(), 1);
        assert_eq!(slice.firings.len(), 3, "recreate, reconcile, and delete");
        assert_eq!(slice.equalities.len(), 1);
        let equality = slice.equality_records.values().next().unwrap();
        assert_eq!(equality.left.term, equality.right.term);
        assert_ne!(equality.left.raw, equality.right.raw);
        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn parent_alias_waits_for_child_key_bridge_without_borrowing_parent_anchor() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64) (H E))
                 (relation Seed (E))
                 (relation New (E))
                 (relation Trigger ())
                 (relation R (E))
                 (relation Out (E))
                 (ruleset bridge_rules)
                 (ruleset emit_rules)
                 (ruleset consume_rules)
                 (Seed (H (A 0)))
                 (New (A 1))
                 (Trigger)
                 (rule ((Trigger))
                       ((union (A 0) (A 1)))
                       :ruleset bridge_rules :name \"bridge\")
                 (rule ((New child))
                       ((R (H child)))
                       :ruleset emit_rules :name \"emit\")
                 (rule ((R value))
                       ((Out value))
                       :ruleset consume_rules :name \"consume\")
                 (run bridge_rules 1)
                 (run emit_rules 1)
                 (run consume_rules 1)
                 (check (Out value))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.equalities.len(), 1, "retain the child key bridge");
        let consume_windows = slice
            .firing_term_windows
            .values()
            .find(|bindings| bindings.len() == 1 && bindings[0].len() == 2)
            .expect("consume must retain the child and parent call windows");
        let [child, parent] = consume_windows[0].as_ref() else {
            unreachable!("window count was checked above")
        };
        assert!(
            child.support_ready_after <= child.available_after,
            "the child's output bridge belongs to its parent's key readiness, not its own capture bound: {consume_windows:?}"
        );
        assert!(
            parent.support_ready_after > parent.available_after,
            "the old H producer exists before its requested child spelling becomes replay-addressable: {consume_windows:?}"
        );
        assert!(
            parent.support_ready_after > child.available_after,
            "the parent must wait for the child denotation bridge, not merely child creation: {consume_windows:?}"
        );

        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        let rendered = crate::slicing::replay::ReplayProgram::render_commands(&commands).unwrap();
        let bridge = rendered
            .find("(run-schedule (run-rule (\"bridge\"")
            .unwrap();
        let parent_alias = rendered[bridge..]
            .find("(H $__slice_replay_")
            .map(|offset| bridge + offset)
            .expect("the H alias must be captured after its child bridge");
        let consume = rendered
            .find("(run-schedule (run-rule (\"consume\"")
            .unwrap();
        assert!(
            bridge < parent_alias && parent_alias < consume,
            "{rendered}"
        );

        drop(egraph);
        let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn post_deletion_equality_cannot_select_stale_child_producer() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64) (B i64) (H E))
                 (relation Old (E))
                 (relation New (E))
                 (relation Target (E))
                 (relation Trigger ())
                 (relation Held (E))
                 (relation Deleted ())
                 (relation Out (E))
                 (ruleset cleanup_old)
                 (ruleset recreate_a)
                 (ruleset early_bridge)
                 (ruleset make_h)
                 (ruleset delete_live)
                 (ruleset late_bridge)
                 (ruleset consume)
                 (Old (A 1))
                 (Target (B 0))
                 (Trigger)
                 (rule ((Trigger))
                       ((delete (A 1)))
                       :ruleset cleanup_old :name \"cleanup-old\")
                 (rule ((Trigger))
                       ((New (A 1)))
                       :ruleset recreate_a :name \"recreate-a\")
                 (rule ((New new) (Target target))
                       ((union new target))
                       :ruleset early_bridge :name \"early-bridge\")
                 (rule ((New child))
                       ((Held (H child)))
                       :ruleset make_h :name \"make-h\")
                 (rule ((Held value))
                       ((delete (H (A 1))) (delete (A 1)) (Deleted))
                       :ruleset delete_live :name \"delete-live\")
                 (rule ((Old old) (Target target) (Deleted))
                       ((union old target))
                       :ruleset late_bridge :name \"late-bridge\")
                 (rule ((Held value) (Deleted))
                       ((Out value))
                       :ruleset consume :name \"consume\")
                 (run cleanup_old 1)
                 (run recreate_a 1)
                 (run early_bridge 1)
                 (run make_h 1)
                 (run delete_live 1)
                 (run late_bridge 1)
                 (run consume 1)
                 (check (Out value))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        // The late old-A=B equality is irrelevant. In particular, it must not
        // make the dead old A occurrence win over the recreated A occurrence
        // that addressed H's key while H was still live.
        assert_eq!(slice.replay_equalities.len(), 1);
        assert_eq!(slice.replay_removals.len(), 2);
        let h_windows = slice
            .firing_term_windows
            .values()
            .flat_map(|bindings| bindings.iter())
            .filter(|windows| windows.len() == 2)
            .map(|windows| windows[1])
            .collect::<Vec<_>>();
        assert_eq!(
            h_windows.len(),
            2,
            "delete-live and consume must each retain child and H windows"
        );
        for h_window in h_windows {
            let live_before = h_window
                .live_before
                .expect("the selected H deletion must bound its producer window");
            assert!(h_window.producer.is_some());
            assert!(
                h_window.support_ready_after < live_before,
                "H's child/key support must fit before H is deleted: {h_window:?}"
            );
        }

        let mut crossed = slice.clone();
        let mut crossed_any = false;
        for bindings in crossed.firing_term_windows.values_mut() {
            for windows in bindings.iter_mut().filter(|windows| windows.len() == 2) {
                if let Some(live_before) = windows[1].live_before {
                    windows[1].support_ready_after = live_before;
                    crossed_any = true;
                }
            }
        }
        assert!(crossed_any);
        let error = crate::slicing::replay::build_replay_program(&egraph, &crossed).unwrap_err();
        assert!(
            error.to_string().contains(
                "no retained pre-wave point in its availability/readiness/liveness window"
            ),
            "{error}"
        );

        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        let rendered = crate::slicing::replay::ReplayProgram::render_commands(&commands).unwrap();
        let h_alias = rendered
            .lines()
            .position(|line| line.starts_with("(let-check ") && line.contains("(H "))
            .expect("H must be captured while its producer row is live");
        let delete_live = rendered
            .lines()
            .position(|line| line.contains("(run-rule (\"delete-live\""))
            .expect("the selected H deletion must replay");
        assert!(h_alias < delete_live, "{rendered}");
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn duplicate_syntax_in_one_binding_keeps_distinct_occurrence_windows() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64) (Pair E E))
                 (relation Old (E))
                 (relation New (E))
                 (relation Trigger ())
                 (relation Pairs (E))
                 (relation Out (E))
                 (ruleset cleanup)
                 (ruleset recreate)
                 (ruleset pair_rules)
                 (ruleset consume_rules)
                 (Old (A 1))
                 (Trigger)
                 (rule ((Trigger))
                       ((delete (A 1)))
                       :ruleset cleanup :name \"cleanup\")
                 (rule ((Trigger))
                       ((New (A 1)))
                       :ruleset recreate :name \"recreate\")
                 (rule ((Old old) (New new))
                       ((Pairs (Pair old new)))
                       :ruleset pair_rules :name \"pair\")
                 (rule ((Pairs pair)) ((Out pair))
                       :ruleset consume_rules :name \"consume\")
                 (run cleanup 1)
                 (run recreate 1)
                 (run pair_rules 1)
                 (run consume_rules 1)
                 (check (Out pair))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        let consume_windows = slice
            .firing_term_windows
            .values()
            .find(|bindings| bindings.len() == 1 && bindings[0].len() == 3)
            .expect("consume must retain two child occurrences and their parent");
        let [old_child, recreated_child, parent] = consume_windows[0].as_ref() else {
            unreachable!("window count was checked above")
        };
        assert!(
            old_child.available_after < recreated_child.available_after
                && recreated_child.available_after < parent.available_after,
            "old child, recreated child, and parent need distinct occurrence-local bounds: {consume_windows:?}"
        );
        assert!(
            old_child.support_ready_after <= old_child.available_after
                && recreated_child.support_ready_after <= recreated_child.available_after,
            "a parent's later anchor must not become either child's replay-readiness bound: {consume_windows:?}"
        );
        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        let rendered = crate::slicing::replay::ReplayProgram::render_commands(&commands).unwrap();
        assert!(
            rendered.contains(
                "(run-schedule (run-rule (\"pair\" ((old $__slice_replay_0) (new $__slice_replay_1)))))"
            ),
            "the pair firing must keep the two source occurrence aliases:\n{rendered}"
        );
        assert!(
            rendered.contains(
                "(let-check $__slice_replay_2 (Pair $__slice_replay_0 $__slice_replay_1) :sort E)"
            ),
            "the parent recipe must preserve its old/new child occurrence windows:\n{rendered}"
        );
        let cleanup = rendered
            .find("(run-schedule (run-rule (\"cleanup\"")
            .unwrap();
        let recreate = rendered
            .find("(run-schedule (run-rule (\"recreate\"")
            .unwrap();
        let pair = rendered.find("(run-schedule (run-rule (\"pair\"").unwrap();
        let consume = rendered
            .find("(run-schedule (run-rule (\"consume\"")
            .unwrap();
        assert!(cleanup < recreate && recreate < pair && pair < consume);

        let aliases_before_cleanup = rendered[..cleanup].matches("(let-check ").count();
        let aliases_between_recreate_and_pair =
            rendered[recreate..pair].matches("(let-check ").count();
        let aliases_between_pair_and_consume =
            rendered[pair..consume].matches("(let-check ").count();
        assert!(
            aliases_before_cleanup >= 1,
            "old occurrence must be named before deletion"
        );
        assert!(
            aliases_between_recreate_and_pair >= 1,
            "recreated occurrence must be named after its creator"
        );
        assert!(
            aliases_between_pair_and_consume >= 1,
            "parent occurrence must be named after its creator"
        );
        assert!(
            rendered.matches("(A 1) :sort E").count() >= 2,
            "identical syntax before and after recreation must keep distinct aliases:\n{rendered}"
        );
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn noninterfering_and_dead_write_deletes_are_not_retained() {
        for program in [
            "(function f (i64) i64 :merge (max old new))
             (relation Trigger (Unit))
             (relation Before (i64))
             (set (f 1) 5)
             (Trigger ())
             (rule ((= value (f 1))) ((Before value)) :name \"observe\")
             (rule ((Trigger u)) ((delete (f 1))) :name \"delete-f\")
             (run 1)
             (check (Before 5))",
            "(function f (i64) i64 :merge (max old new))
             (relation Trigger (Unit))
             (relation Write (Unit))
             (relation Independent (Unit))
             (relation Out (Unit))
             (set (f 1) 5)
             (Trigger ())
             (Write ())
             (Independent ())
             (rule ((Trigger u)) ((delete (f 1))) :name \"delete-f\")
             (rule ((Write u)) ((set (f 1) 2)) :name \"dead-write\")
             (rule ((Independent u)) ((Out ())) :name \"make-out\")
             (run 1)
             (check (Out ()))",
        ] {
            let mut egraph = EGraph::default();
            serial_trace_pool()
                .install(|| egraph.enable_trace())
                .unwrap();
            egraph.parse_and_run_program(None, program).unwrap();
            let bridge = egraph
                .backend
                .as_any()
                .downcast_ref::<egglog_bridge::EGraph>()
                .unwrap();
            bridge
                .with_trace_view(|view| {
                    assert_eq!(view.totals().removals, 1);
                    Ok(())
                })
                .unwrap();
            let slice = slice_all_checks(&egraph).unwrap();
            assert!(slice.replay_removals.is_empty());
        }
    }

    #[test]
    fn merge_old_noop_is_retained_only_with_an_effective_sibling() {
        let mut effective_sibling = EGraph::default();
        serial_trace_pool()
            .install(|| effective_sibling.enable_trace())
            .unwrap();
        effective_sibling
            .parse_and_run_program(
                None,
                "(function f (i64) i64 :merge old)
                 (relation Trigger (Unit))
                 (relation Out (Unit))
                 (set (f 1) 5)
                 (Trigger ())
                 (rule ((Trigger u)) ((set (f 1) 2) (Out ())) :name \"noop-with-sibling\")
                 (run 1)
                 (check (Out ()))",
            )
            .unwrap();
        let slice = slice_all_checks(&effective_sibling).unwrap();
        assert_eq!(slice.firings.len(), 1);
        let firing = *slice.firings.iter().next().unwrap();
        let bridge = effective_sibling
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        bridge
            .with_trace_view(|view| {
                let reads = view.firing(firing)?.merge_reads;
                assert_eq!(reads.len(), 1);
                assert!(slice.facts.contains(&reads[0]));
                Ok(())
            })
            .unwrap();

        let mut noop_only = EGraph::default();
        serial_trace_pool()
            .install(|| noop_only.enable_trace())
            .unwrap();
        noop_only
            .parse_and_run_program(
                None,
                "(function f (i64) i64 :merge old)
                 (relation Trigger (Unit))
                 (relation Keep (Unit))
                 (set (f 1) 5)
                 (Trigger ())
                 (Keep ())
                 (rule ((Trigger u)) ((set (f 1) 2)) :name \"noop-only\")
                 (run 1)
                 (check (Keep ()))",
            )
            .unwrap();
        let slice = slice_all_checks(&noop_only).unwrap();
        assert!(slice.firings.is_empty());
        // The lower-level recorder contract (including zero durable promotion)
        // is covered by `unchanged_merge_without_effective_sibling_promotes_nothing`.
        // Here the frontend contract is that an unrelated check never selects
        // or replays the no-op-only firing.
    }

    #[test]
    fn same_term_child_occurrences_keep_their_native_bridge() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64) (H E))
                 (relation Trigger ())
                 (relation Old (E))
                 (relation New (E))
                 (relation R (E))
                 (relation S (E))
                 (relation Out ())
                 (ruleset cleanup)
                 (ruleset recreate)
                 (ruleset bridge)
                 (ruleset emit)
                 (ruleset consume)
                 (Trigger)
                 (Old (A 1))
                 (R (H (A 1)))
                 (rule ((Trigger))
                       ((delete (A 1)))
                       :ruleset cleanup
                       :name \"cleanup\")
                 (rule ((Trigger))
                       ((New (A 1)))
                       :ruleset recreate
                       :name \"recreate\")
                 (rule ((Old x) (New y))
                       ((union x y))
                       :ruleset bridge
                       :name \"bridge\")
                 (rule ((New y))
                       ((S (H y)))
                       :ruleset emit
                       :name \"emit\")
                 (rule ((R x) (S x))
                       ((Out))
                       :ruleset consume
                       :name \"consume\")
                 (run cleanup 1)
                 (run recreate 1)
                 (run bridge 1)
                 (run emit 1)
                 (run consume 1)
                 (check (Out))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.equalities.len(), 1, "retain the A occurrence bridge");
        let mut damaged = slice.clone();
        damaged.equalities.clear();
        assert!(matches!(
            damaged.validate_exact_support(),
            Err(SliceError::MissingSupport {
                kind: "applied equality",
                ..
            })
        ));
        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn relational_check_shared_variable_equality_is_retained() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64) (B i64))
                 (relation R (E))
                 (relation S (E))
                 (rule () ((union (A 1) (B 2))) :name \"eq-ab\")
                 (R (A 1))
                 (S (B 2))
                 (run 1)
                 (check (R x) (S x))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.firings.len(), 1);
        assert_eq!(slice.equalities.len(), 1);
    }

    #[test]
    fn selected_firing_exposes_whole_head_without_causal_closing_sibling() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation A (Unit))
                 (relation Out (Unit))
                 (relation Sibling (Unit))
                 (A ())
                 (rule ((A u)) ((Out ()) (Sibling ())) :name \"two-effects\")
                 (run 1)
                 (check (Out ()))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        assert_eq!(slice.firings.len(), 1);
        assert_eq!(slice.facts.len(), 2, "only the check cone is causal");
        assert_eq!(
            slice.replay_facts.len(),
            3,
            "the sibling head effect is visible"
        );
    }

    #[test]
    fn no_merge_rewrite_retains_the_interfering_delete() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(function f (i64) i64 :no-merge)
                 (relation Trigger (Unit))
                 (relation Write (Unit))
                 (relation Done (Unit))
                 (relation Before (i64))
                 (relation After (i64))
                 (set (f 1) 5)
                 (Trigger ())
                 (Write ())
                 (rule ((= value (f 1))) ((Before value)) :name \"observe-before\")
                 (rule ((Trigger u)) ((delete (f 1))) :name \"delete-f\")
                 (rule ((Write u)) ((set (f 1) 2) (Done ())) :name \"rewrite-f\")
                 (rule ((Done u) (= value (f 1))) ((After value)) :name \"observe-after\")
                 (run 2)
                 (check (Before 5) (After 2))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        assert_eq!(slice.firings.len(), 4);
        assert_eq!(slice.replay_removals.len(), 1);
    }

    #[test]
    fn direct_check_retains_nested_child_equality_used_by_a_head_term() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64) (Alias i64))
                 (sort Es (Vec E))
                 (datatype Root (Target Es) (Seed))
                 (ruleset equate)
                 (ruleset finish)
                 (let $seed (Seed))
                 (A 8)
                 (rewrite (A x) (Alias x) :ruleset equate)
                 (rule ()
                       ((union $seed (Target (vec-of (Alias 8)))))
                       :ruleset finish
                       :name \"finish\")
                 (run equate 1)
                 (run finish 1)
                 (check (= $seed (Target (vec-of (A 8)))))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(
            slice.firings.len(),
            2,
            "the parent union and nested A/Alias equality are both required"
        );
        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn eqsort_result_of_replay_safe_primitive_is_structurally_available() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64))
                 (sort Es (Vec E))
                 (relation Seed (Es))
                 (relation Out (E))
                 (Seed (vec-of (A 1)))
                 (rule ((Seed xs)
                        (= x (vec-get xs 0)))
                       ((Out x))
                       :name \"read-vec\")
                 (run 1)
                 (check (Out (A 1)))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.firings.len(), 1);
        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn repeated_pure_result_guards_share_one_naming_recipe() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation Input (i64))
                 (relation Out (i64))
                 (Input 1)
                 (rule ((Input n)
                        (= x (+ n 1))
                        (= x (* n 2)))
                       ((Out x))
                       :name \"agreeing-guards\")
                 (run 1)
                 (check (Out 2))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.firings.len(), 1);
        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn eqsort_projection_retains_the_child_equality_it_observed() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        serial_trace_pool()
            .install(|| {
                egraph.parse_and_run_program(
                    None,
                    "(datatype E (A) (B))
                 (sort Es (Vec E))
                 (relation Inputs (E E))
                 (relation Out ())
                 (ruleset equate)
                 (ruleset make)
                 (ruleset consume)
                 (rule () ((union (A) (B)))
                       :ruleset equate :name \"equate\")
                 (rule ()
                       ((Inputs (vec-get (vec-of (A)) 0)
                                (vec-get (vec-of (B)) 0)))
                       :ruleset make :name \"make\")
                 (rule ((Inputs x x)) ((Out))
                       :ruleset consume :name \"consume\")
                 (run equate 1)
                 (run make 1)
                 (run consume 1)
                 (check (Out))",
                )
            })
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.firings.len(), 3);
        assert_eq!(slice.equalities.len(), 1);
        let mut damaged = slice.clone();
        damaged.equalities.clear();
        assert!(matches!(
            damaged.validate_exact_support(),
            Err(SliceError::MissingSupport {
                kind: "applied equality",
                ..
            })
        ));
        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn congruence_projection_retains_historical_child_union() {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (Num i64) (Add E E) (Max E E))
                 (rewrite (Add (Num a) (Num b)) (Num (+ a b)))
                 (rewrite (Max (Num a) (Num b)) (Num (max a b)))
                 (datatype L (Cons L))
                 (constructor Nil () L)
                 (constructor F (i64 L) E)
                 (rule ((= f (F capacity (Cons rest))))
                       ((union f
                               (Max (Add (Num 1) (F (- capacity 1) rest))
                                    (F capacity rest)))))
                 (rule ((= f (F capacity (Nil))))
                       ((union f (Num 0))))
                 (let $test (F 2 (Cons (Cons (Nil)))))
                 (run 10)
                 (check (= $test (Num 2)))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
        serial_trace_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }
}

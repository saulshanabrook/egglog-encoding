//! Backward dynamic slicing from recorded criteria.
//!
//! A slice selects one sound historical support cone. It does not claim global
//! minimality and does not construct a proof.

use std::collections::VecDeque;

use crate::core_relations::{
    AppliedEqualityId, CauseRef, Criterion, CriterionEndpointOccurrence, EdgeHorizon,
    EqualityEndpoint, EqualityReason, FactCellRef, FactId, FiringEqualitySource, FiringId,
    HistoryPosition, PremiseOccurrence, ProjectedAppliedEquality, RawAliasWindow, RawCause,
    RawEqualityEndpoint, RawEqualitySupport, ReplayTableKind, ReplayTermId, SourceRef, TableId,
    TraceView, TraceViewError, TypedCellEquality, Value,
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
    let premise_cell = |occurrence: PremiseOccurrence| -> Result<FactCellRef, TraceViewError> {
        let fact = *premises.get(occurrence.premise).ok_or_else(|| {
            TraceViewError::Invalid(format!(
                "equality obligation cites missing premise {}",
                occurrence.premise
            ))
        })?;
        let column = occurrence
            .column
            .try_into()
            .map_err(|_| TraceViewError::Invalid("premise occurrence column exceeds u32".into()))?;
        Ok(FactCellRef {
            fact,
            column: crate::core_relations::ColumnId::new(column),
        })
    };
    match (left, right) {
        (FiringEqualitySource::Premise(left), FiringEqualitySource::Premise(right)) => view
            .explain_fact_cell_support_at(
                premise_cell(left)?,
                premise_cell(right)?,
                as_of_edges,
                position,
            ),
        (FiringEqualitySource::Premise(fact), FiringEqualitySource::Constant(endpoint))
        | (FiringEqualitySource::Constant(endpoint), FiringEqualitySource::Premise(fact)) => view
            .explain_fact_endpoint_support_at(premise_cell(fact)?, endpoint, as_of_edges, position),
        (FiringEqualitySource::Constant(left), FiringEqualitySource::Constant(right)) => {
            view.explain_equality_support_at(left, right, as_of_edges, position)
        }
    }
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
    if !slice.equality_records.contains_key(&id) {
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
    for event in slice.equality_records.values() {
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
            .any(|edge| !slice.equality_records.contains_key(edge))
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
        if slice.equality_records.contains_key(&id) {
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
#[path = "backward_tests.rs"]
mod tests;

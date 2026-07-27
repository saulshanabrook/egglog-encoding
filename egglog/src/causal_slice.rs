use std::collections::VecDeque;

use crate::core_relations::{
    AppliedEqualityId, CausalReceiptView, CheckEndpointOccurrence, CheckRoot, EqualityEdgeCount,
    EqualityEndpoint, EqualityReason, FactCellRef, FactId, HistoryPosition,
    ProjectedAppliedEquality, RawAliasWindow, RawEqualityEndpoint, RawEqualitySupport,
    RawReceiptCause, ReceiptCausePrior, ReceiptCauseRef, ReceiptEqualitySource, ReceiptViewError,
    ReplaySortId, ReplayTableKind, ReplayTermId, RuleMatchId, SourceRef, TableId,
    TypedCellEquality, Value,
};
use crate::numeric_id::NumericId;
use crate::util::{HashMap, HashSet};

use crate::EGraph;

#[derive(Clone, Debug, PartialEq, Eq)]
struct SupportRequirement {
    applied: Box<[AppliedEqualityId]>,
    facts: Box<[FactId]>,
    causes: Box<[ReceiptCauseRef]>,
    rekeys: Box<[HistoryPosition]>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CausalSlice {
    pub(crate) checks: HashSet<u32>,
    pub(crate) check_positions: HashMap<u32, HistoryPosition>,
    pub(crate) facts: HashSet<FactId>,
    pub(crate) matches: HashSet<RuleMatchId>,
    pub(crate) equalities: HashSet<AppliedEqualityId>,
    pub(crate) replay_facts: HashSet<FactId>,
    pub(crate) replay_equalities: HashSet<AppliedEqualityId>,
    pub(crate) replay_removals: HashSet<usize>,
    pub(crate) interference_removals: HashSet<usize>,
    pub(crate) rekeys: HashSet<HistoryPosition>,
    pub(crate) causes: HashSet<ReceiptCauseRef>,
    pub(crate) sources: HashSet<SourceRef>,
    pub(crate) fact_terms: HashMap<FactId, Box<[ReplayTermId]>>,
    pub(crate) match_terms: HashMap<RuleMatchId, Box<[ReplayTermId]>>,
    /// Earliest historical capture point for each occurrence in each match
    /// binding's structural `let-check` recipe. Aliases may be hoisted before
    /// a selected deletion and then reused by later grounded waves.
    pub(crate) match_term_windows: HashMap<RuleMatchId, Box<[Box<[RawAliasWindow]>]>>,
    pub(crate) equality_records: HashMap<AppliedEqualityId, ProjectedAppliedEquality>,
    interfering_cell_count: usize,
    delete_cone_match_count: usize,
    requirements: Vec<SupportRequirement>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CausalSliceStats {
    pub(crate) selected_checks: u64,
    pub(crate) causal_facts: u64,
    pub(crate) causal_matches: u64,
    pub(crate) causal_equalities: u64,
    pub(crate) replay_facts: u64,
    pub(crate) replay_equalities: u64,
    pub(crate) replay_removals: u64,
    pub(crate) interference_removals: u64,
    pub(crate) interfering_cells: u64,
    pub(crate) delete_cone_matches: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ReplayOwner {
    Match(RuleMatchId),
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
struct TypedTerm {
    sort: ReplaySortId,
    term: ReplayTermId,
    raw: Value,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum KeyCell {
    Base(Value),
    Equality(TypedTerm),
}

#[derive(Default)]
struct SelectedEqualityDsu {
    parent: HashMap<TypedTerm, TypedTerm>,
}

impl SelectedEqualityDsu {
    fn find(&mut self, term: TypedTerm) -> TypedTerm {
        let parent = *self.parent.entry(term).or_insert(term);
        if parent == term {
            return term;
        }
        let root = self.find(parent);
        self.parent.insert(term, root);
        root
    }

    fn union(&mut self, left: TypedTerm, right: TypedTerm) -> bool {
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

    fn canonical(&mut self, cell: KeyCell) -> KeyCell {
        match cell {
            KeyCell::Base(_) => cell,
            KeyCell::Equality(term) => KeyCell::Equality(self.find(term)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum CausalSliceError {
    #[error(transparent)]
    Receipt(#[from] ReceiptViewError),
    #[error("causal slicing requires the concrete main bridge backend")]
    UnsupportedBackend,
    #[error("causal slicing cannot use a poisoned capture: {0}")]
    Poisoned(String),
    #[error("selected causal support is missing {kind} {id}")]
    MissingSupport { kind: &'static str, id: u64 },
}

impl CausalSlice {
    pub(crate) fn stats(&self) -> CausalSliceStats {
        CausalSliceStats {
            selected_checks: self.checks.len() as u64,
            causal_facts: self.facts.len() as u64,
            causal_matches: self.matches.len() as u64,
            causal_equalities: self.equalities.len() as u64,
            replay_facts: self.replay_facts.len() as u64,
            replay_equalities: self.replay_equalities.len() as u64,
            replay_removals: self.replay_removals.len() as u64,
            interference_removals: self.interference_removals.len() as u64,
            interfering_cells: self.interfering_cell_count as u64,
            delete_cone_matches: self.delete_cone_match_count as u64,
        }
    }

    pub(crate) fn validate_exact_support(&self) -> Result<(), CausalSliceError> {
        for requirement in &self.requirements {
            for id in &requirement.applied {
                if !self.equalities.contains(id) {
                    return Err(CausalSliceError::MissingSupport {
                        kind: "applied equality",
                        id: id.get(),
                    });
                }
            }
            for id in &requirement.facts {
                if !self.facts.contains(id) {
                    return Err(CausalSliceError::MissingSupport {
                        kind: "fact",
                        id: id.get(),
                    });
                }
            }
            for id in &requirement.causes {
                if !self.causes.contains(id) {
                    let raw = match id {
                        ReceiptCauseRef::Rule(rule) => rule.get(),
                        ReceiptCauseRef::Cause(cause) => cause.get() as u64,
                    };
                    return Err(CausalSliceError::MissingSupport {
                        kind: "cause",
                        id: raw,
                    });
                }
            }
            for position in &requirement.rekeys {
                if !self.rekeys.contains(position) {
                    return Err(CausalSliceError::MissingSupport {
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
    Matched(RuleMatchId),
    Cause(ReceiptCauseRef),
    Equality(AppliedEqualityId),
    Rekey(HistoryPosition),
}

fn enqueue_support(
    slice: &mut CausalSlice,
    work: &mut VecDeque<Work>,
    support: RawEqualitySupport,
) {
    for id in &support.applied {
        work.push_back(Work::Equality(*id));
    }
    for id in &support.facts {
        work.push_back(Work::Fact(*id));
    }
    for cause in &support.causes {
        work.push_back(Work::Cause(*cause));
    }
    for position in &support.rekeys {
        work.push_back(Work::Rekey(*position));
    }
    slice.requirements.push(SupportRequirement {
        applied: support.applied,
        facts: support.facts,
        causes: support.causes,
        rekeys: support.rekeys,
    });
}

fn check_occurrence_cell(occurrence: CheckEndpointOccurrence) -> Option<FactCellRef> {
    match occurrence {
        CheckEndpointOccurrence::FactCell(cell) => Some(cell),
        CheckEndpointOccurrence::Current => None,
    }
}

fn explain_rule_equality(
    view: &mut CausalReceiptView<'_>,
    left: ReceiptEqualitySource,
    right: ReceiptEqualitySource,
    premises: &[FactId],
    as_of_edges: EqualityEdgeCount,
    position: HistoryPosition,
) -> Result<RawEqualitySupport, ReceiptViewError> {
    let premise_cell =
        |source: ReceiptEqualitySource| -> Result<Option<FactCellRef>, ReceiptViewError> {
            let ReceiptEqualitySource::Premise(occurrence) = source else {
                return Ok(None);
            };
            let fact = *premises.get(occurrence.premise).ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "equality obligation cites missing premise {}",
                    occurrence.premise
                ))
            })?;
            let column = occurrence.column.try_into().map_err(|_| {
                ReceiptViewError::Invalid("premise occurrence column exceeds u32".into())
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
            let ReceiptEqualitySource::Constant(endpoint) = right else {
                unreachable!("non-premise equality source is always a constant")
            };
            return view.explain_fact_endpoint_support_at(fact, endpoint, as_of_edges, position);
        }
        (None, Some(fact)) => {
            let ReceiptEqualitySource::Constant(endpoint) = left else {
                unreachable!("non-premise equality source is always a constant")
            };
            return view.explain_fact_endpoint_support_at(fact, endpoint, as_of_edges, position);
        }
        (None, None) => {}
    }

    let mut facts = Vec::new();
    let mut rekeys = Vec::new();
    let mut resolve = |source| -> Result<EqualityEndpoint, ReceiptViewError> {
        match source {
            ReceiptEqualitySource::Premise(occurrence) => {
                let fact = *premises.get(occurrence.premise).ok_or_else(|| {
                    ReceiptViewError::Invalid(format!(
                        "equality obligation cites missing premise {}",
                        occurrence.premise
                    ))
                })?;
                let column = occurrence.column.try_into().map_err(|_| {
                    ReceiptViewError::Invalid("premise occurrence column exceeds u32".into())
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
            ReceiptEqualitySource::Constant(endpoint) => Ok(endpoint),
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
        causes: support.causes,
        rekeys: rekeys.into_boxed_slice(),
    })
}

fn replay_owner_for_cause(
    view: &CausalReceiptView<'_>,
    cause: ReceiptCauseRef,
    memo: &mut HashMap<ReceiptCauseRef, Option<ReplayOwner>>,
    active: &mut HashSet<ReceiptCauseRef>,
) -> Result<Option<ReplayOwner>, ReceiptViewError> {
    if let Some(owner) = memo.get(&cause) {
        return Ok(owner.clone());
    }
    if !active.insert(cause) {
        return Err(ReceiptViewError::Invalid(format!(
            "receipt cause cycle reaches {cause:?}"
        )));
    }
    let owner = match cause {
        ReceiptCauseRef::Rule(rule) => Some(ReplayOwner::Match(rule)),
        ReceiptCauseRef::Cause(id) => match view.cause(id)? {
            RawReceiptCause::Source(source) => Some(ReplayOwner::Source(source.clone())),
            RawReceiptCause::Merge { incoming, .. } => {
                replay_owner_for_cause(view, incoming, memo, active)?
            }
            RawReceiptCause::Rebuild { .. }
            | RawReceiptCause::ContainerCanonicalize { .. }
            | RawReceiptCause::ContainerRefresh { .. } => None,
        },
    };
    active.remove(&cause);
    memo.insert(cause, owner.clone());
    Ok(owner)
}

fn build_owner_index(view: &CausalReceiptView<'_>) -> Result<OwnerIndex, ReceiptViewError> {
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
            EqualityReason::RuleUnion(rule) => Some(ReplayOwner::Match(rule)),
            EqualityReason::SourceUnion { cause }
            | EqualityReason::MergeFn { cause }
            | EqualityReason::Congruence { cause, .. } => {
                replay_owner_for_cause(view, ReceiptCauseRef::Cause(cause), &mut memo, &mut active)?
            }
        };
        if let Some(owner) = owner {
            index.entry(owner).or_default().equalities.push(equality);
        }
    }
    for removal in 0..totals.removals as usize {
        let owner = ReplayOwner::Match(view.removal(removal)?.cause);
        index.entry(owner).or_default().removals.push(removal);
    }
    Ok(index)
}

fn mark_owner_visible(
    view: &mut CausalReceiptView<'_>,
    index: &OwnerIndex,
    slice: &mut CausalSlice,
    owner: &ReplayOwner,
) -> Result<(), ReceiptViewError> {
    let Some(effects) = index.get(owner) else {
        return Ok(());
    };
    slice.replay_facts.extend(effects.facts.iter().copied());
    for id in effects.equalities.iter().copied() {
        if slice.replay_equalities.insert(id) {
            slice
                .equality_records
                .insert(id, view.project_applied_equality(id)?);
        }
    }
    slice
        .replay_removals
        .extend(effects.removals.iter().copied());
    Ok(())
}

fn selected_equality_dsu(slice: &CausalSlice) -> SelectedEqualityDsu {
    let mut dsu = SelectedEqualityDsu::default();
    for id in &slice.replay_equalities {
        let event = &slice.equality_records[id];
        dsu.union(
            TypedTerm {
                sort: event.left.sort,
                term: event.left.term,
                raw: event.left.raw,
            },
            TypedTerm {
                sort: event.right.sort,
                term: event.right.term,
                raw: event.right.raw,
            },
        );
    }
    dsu
}

fn equality_landmark_is_replay_visible(
    view: &mut CausalReceiptView<'_>,
    slice: &CausalSlice,
    as_of_edges: EqualityEdgeCount,
    position: HistoryPosition,
    equalities: &[TypedCellEquality],
) -> Result<bool, ReceiptViewError> {
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
    view: &mut CausalReceiptView<'_>,
    slice: &CausalSlice,
    cause: ReceiptCauseRef,
    current_event: AppliedEqualityId,
    active: &mut HashSet<ReceiptCauseRef>,
) -> Result<bool, ReceiptViewError> {
    if !active.insert(cause) {
        return Err(ReceiptViewError::Invalid(format!(
            "receipt cause cycle reaches {cause:?}"
        )));
    }
    let visible = match cause {
        ReceiptCauseRef::Rule(rule) => slice.matches.contains(&rule),
        ReceiptCauseRef::Cause(id) => match view.cause(id)? {
            RawReceiptCause::Source(source) => slice.sources.contains(source),
            RawReceiptCause::Merge { incoming, prior } => {
                let incoming = maintenance_cause_is_replay_visible(
                    view,
                    slice,
                    incoming,
                    current_event,
                    active,
                )?;
                let prior = match prior {
                    ReceiptCausePrior::Fact(fact) => slice.replay_facts.contains(&fact),
                    ReceiptCausePrior::Cause(cause) => maintenance_cause_is_replay_visible(
                        view,
                        slice,
                        cause,
                        current_event,
                        active,
                    )?,
                };
                incoming && prior
            }
            RawReceiptCause::Rebuild {
                prior_fact,
                as_of_edges,
                position,
                equalities,
                ..
            }
            | RawReceiptCause::ContainerRefresh {
                prior_fact,
                as_of_edges,
                position,
                equalities,
                ..
            } => {
                if as_of_edges.get() >= current_event.get() {
                    return Err(ReceiptViewError::Invalid(format!(
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
            RawReceiptCause::ContainerCanonicalize {
                as_of_edges,
                position,
                equalities,
                ..
            } => {
                if as_of_edges.get() >= current_event.get() {
                    return Err(ReceiptViewError::Invalid(format!(
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
    view: &mut CausalReceiptView<'_>,
    slice: &mut CausalSlice,
) -> Result<bool, ReceiptViewError> {
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
                ReceiptCauseRef::Cause(cause)
            }
        };
        debug_assert!(active.is_empty());
        if !maintenance_cause_is_replay_visible(view, slice, cause, id, &mut active)? {
            continue;
        }
        slice.replay_equalities.insert(id);
        slice
            .equality_records
            .insert(id, view.project_applied_equality(id)?);
        selected_any = true;
    }
    Ok(selected_any)
}

fn replay_key_at(
    view: &mut CausalReceiptView<'_>,
    fact: FactId,
    position: HistoryPosition,
) -> Result<(TableId, Box<[KeyCell]>), ReceiptViewError> {
    let record = view.fact(fact)?;
    let table = record.table;
    let values = record.values.to_vec();
    let schema = view.table_schema(table)?;
    let mut key = Vec::with_capacity(schema.key_columns);
    for column in 0..schema.key_columns {
        if schema.columns[column].is_some() {
            let column_id =
                crate::core_relations::ColumnId::new(column.try_into().map_err(|_| {
                    ReceiptViewError::Invalid("table key column exceeds u32".into())
                })?);
            let endpoint = view
                .fact_cell_at(
                    FactCellRef {
                        fact,
                        column: column_id,
                    },
                    position,
                )?
                .endpoint;
            key.push(KeyCell::Equality(TypedTerm {
                sort: endpoint.sort,
                term: endpoint.term,
                raw: endpoint.raw,
            }));
        } else {
            let value = values.get(column).copied().ok_or_else(|| {
                ReceiptViewError::Invalid(format!("fact {fact:?} has no key column {column}"))
            })?;
            key.push(KeyCell::Base(value));
        }
    }
    Ok((table, key.into_boxed_slice()))
}

fn position_before_event(position: HistoryPosition) -> Result<HistoryPosition, ReceiptViewError> {
    position
        .get()
        .checked_sub(1)
        .map(HistoryPosition::new)
        .ok_or_else(|| {
            ReceiptViewError::Invalid("causal event has no preceding history position".into())
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
    view: &mut CausalReceiptView<'_>,
    slice: &mut CausalSlice,
    work: &mut VecDeque<Work>,
) -> Result<bool, ReceiptViewError> {
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
            slice.interference_removals.insert(index);
            work.push_back(Work::Matched(removal.cause));
            selected_any = true;
        }
    }
    Ok(selected_any)
}

fn count_interfering_cells(
    view: &mut CausalReceiptView<'_>,
    slice: &CausalSlice,
) -> Result<usize, ReceiptViewError> {
    let mut dsu = selected_equality_dsu(slice);
    let mut cells = HashSet::default();
    for index in &slice.interference_removals {
        let removal = view.removal(*index)?;
        let victim_position = position_before_event(removal.position)?;
        let (table, key) = replay_key_at(view, removal.removed_fact, victim_position)?;
        let key = key
            .iter()
            .copied()
            .map(|cell| dsu.canonical(cell))
            .collect::<Vec<_>>();
        cells.insert((table, key));
    }
    Ok(cells.len())
}

fn seed_check_root(
    view: &mut CausalReceiptView<'_>,
    slice: &mut CausalSlice,
    work: &mut VecDeque<Work>,
    root: &CheckRoot,
) -> Result<(), ReceiptViewError> {
    slice.checks.insert(root.check);
    slice.check_positions.insert(root.check, root.position);
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
                if let Some(endpoint_equality) = view.explain_equality_support_if_observed_at(
                    left_endpoint,
                    right_endpoint,
                    root.as_of_edges,
                    root.position,
                )? {
                    enqueue_support(slice, work, endpoint_equality);
                }
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

fn slice_roots(
    view: &mut CausalReceiptView<'_>,
    roots: Vec<CheckRoot>,
) -> Result<CausalSlice, ReceiptViewError> {
    let owner_index = build_owner_index(view)?;
    let mut slice = CausalSlice::default();
    let mut work = VecDeque::new();
    for root in &roots {
        seed_check_root(view, &mut slice, &mut work, root)?;
    }

    let mut matches_before_interference = None;
    loop {
        while let Some(item) = work.pop_front() {
            match item {
                Work::Fact(id) => {
                    if !slice.facts.insert(id) {
                        continue;
                    }
                    slice.replay_facts.insert(id);
                    let cause = view.fact(id)?.cause;
                    let terms = view.fact_terms(id)?;
                    slice.fact_terms.insert(id, terms);
                    work.push_back(Work::Cause(cause));
                }
                Work::Matched(id) => {
                    if !slice.matches.insert(id) {
                        continue;
                    }
                    mark_owner_visible(view, &owner_index, &mut slice, &ReplayOwner::Match(id))?;
                    let matched = view.matched(id)?;
                    let rule = matched.rule;
                    let position = matched.position;
                    let as_of_edges = matched.as_of_edges;
                    let premises = matched.premises.to_vec();
                    let merge_reads = matched.merge_reads.to_vec();
                    work.extend(premises.iter().copied().map(Work::Fact));
                    work.extend(merge_reads.into_iter().map(Work::Fact));
                    let terms = view.match_terms(id)?;
                    let mut windows = Vec::with_capacity(terms.len());
                    for binding in 0..terms.len() {
                        let availability = view.explain_match_term_availability(id, binding)?;
                        windows.push(availability.aliases);
                        enqueue_support(&mut slice, &mut work, availability.support);
                    }
                    slice.match_terms.insert(id, terms);
                    slice
                        .match_term_windows
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
                    let ReceiptCauseRef::Cause(id) = cause else {
                        let ReceiptCauseRef::Rule(id) = cause else {
                            unreachable!()
                        };
                        work.push_back(Work::Matched(id));
                        continue;
                    };
                    match view.cause(id)? {
                        RawReceiptCause::Source(source) => {
                            let source = source.clone();
                            slice.sources.insert(source.clone());
                            mark_owner_visible(
                                view,
                                &owner_index,
                                &mut slice,
                                &ReplayOwner::Source(source),
                            )?;
                        }
                        RawReceiptCause::Rebuild {
                            prior_fact,
                            as_of_edges,
                            position,
                            equalities,
                            ..
                        }
                        | RawReceiptCause::ContainerRefresh {
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
                        RawReceiptCause::ContainerCanonicalize {
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
                        RawReceiptCause::Merge { incoming, prior } => {
                            work.push_back(Work::Cause(incoming));
                            work.push_back(match prior {
                                ReceiptCausePrior::Fact(fact) => Work::Fact(fact),
                                ReceiptCausePrior::Cause(cause) => Work::Cause(cause),
                            });
                        }
                    }
                }
                Work::Equality(id) => {
                    if !slice.equalities.insert(id) {
                        continue;
                    }
                    slice.replay_equalities.insert(id);
                    let event = view.project_applied_equality(id)?;
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
                    slice.equality_records.insert(id, event);
                    work.push_back(Work::Cause(match reason {
                        EqualityReason::RuleUnion(rule) => ReceiptCauseRef::Rule(rule),
                        EqualityReason::SourceUnion { cause }
                        | EqualityReason::MergeFn { cause }
                        | EqualityReason::Congruence { cause, .. } => ReceiptCauseRef::Cause(cause),
                    }));
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
        select_replay_maintenance_equalities(view, &mut slice)?;
        let matches_before_interference =
            *matches_before_interference.get_or_insert(slice.matches.len());
        if !select_interfering_removals(view, &mut slice, &mut work)? {
            slice.delete_cone_match_count = slice
                .matches
                .len()
                .saturating_sub(matches_before_interference);
            break;
        }
    }
    slice.interfering_cell_count = count_interfering_cells(view, &slice)?;
    slice
        .validate_exact_support()
        .map_err(|error| ReceiptViewError::Invalid(error.to_string()))?;
    Ok(slice)
}

fn slice_view(
    view: &mut CausalReceiptView<'_>,
    check: u32,
) -> Result<CausalSlice, ReceiptViewError> {
    slice_roots(view, vec![view.check_root(check)?.clone()])
}

fn slice_all_view(view: &mut CausalReceiptView<'_>) -> Result<CausalSlice, ReceiptViewError> {
    let roots = view.check_roots().into_iter().cloned().collect();
    slice_roots(view, roots)
}

pub(crate) fn slice_check(egraph: &EGraph, check: u32) -> Result<CausalSlice, CausalSliceError> {
    egraph
        .causal_state
        .as_ref()
        .ok_or(CausalSliceError::UnsupportedBackend)?
        .ensure_healthy()
        .map_err(|error| CausalSliceError::Poisoned(error.to_string()))?;
    let bridge = egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .ok_or(CausalSliceError::UnsupportedBackend)?;
    bridge
        .with_causal_receipt_view(|view| slice_view(view, check))
        .map_err(CausalSliceError::Receipt)
}

pub(crate) fn slice_all_checks(egraph: &EGraph) -> Result<CausalSlice, CausalSliceError> {
    egraph
        .causal_state
        .as_ref()
        .ok_or(CausalSliceError::UnsupportedBackend)?
        .ensure_healthy()
        .map_err(|error| CausalSliceError::Poisoned(error.to_string()))?;
    let bridge = egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .ok_or(CausalSliceError::UnsupportedBackend)?;
    bridge
        .with_causal_receipt_view(slice_all_view)
        .map_err(CausalSliceError::Receipt)
}

pub(crate) fn slice_all_check_stats(egraph: &EGraph) -> Result<CausalSliceStats, CausalSliceError> {
    slice_all_checks(egraph).map(|slice| slice.stats())
}

#[cfg(test)]
mod tests {
    use std::sync::OnceLock;

    use super::*;

    fn serial_causal_pool() -> &'static rayon::ThreadPool {
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
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        assert_eq!(slice.matches.len(), 2);
        assert_eq!(slice.equalities.len(), 1);
        assert_eq!(slice.sources.len(), 2);
        assert!(slice.matches.iter().all(|matched| {
            let record = slice.match_terms.get(matched).unwrap();
            record.len() <= 1
        }));

        let mut damaged = slice.clone();
        damaged.equalities.clear();
        assert!(matches!(
            damaged.validate_exact_support(),
            Err(CausalSliceError::MissingSupport {
                kind: "applied equality",
                ..
            })
        ));
    }

    #[test]
    fn interfering_same_wave_delete_retains_its_independent_match() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
            .with_causal_receipt_view(|view| {
                assert_eq!(view.totals().removals, 1);
                Ok(())
            })
            .unwrap();
        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(
            slice.matches.len(),
            4,
            "the independent delete must be rooted"
        );
        assert_eq!(
            slice.stats(),
            CausalSliceStats {
                selected_checks: 1,
                causal_facts: slice.facts.len() as u64,
                causal_matches: 4,
                causal_equalities: 0,
                replay_facts: slice.replay_facts.len() as u64,
                replay_equalities: 0,
                replay_removals: 1,
                interference_removals: 1,
                interfering_cells: 1,
                delete_cone_matches: 1,
            }
        );
    }

    #[test]
    fn all_checks_union_disjoint_cones_and_preserve_positions() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        assert_eq!(slice.check_positions.len(), 2);
        assert!(slice.check_positions[&0] < slice.check_positions[&1]);
        assert_eq!(slice.matches.len(), 2);
        let stats = slice_all_check_stats(&egraph).unwrap();
        assert_eq!(stats.selected_checks, 2);
        assert_eq!(stats.causal_matches, 2);
    }

    #[test]
    fn future_selected_child_union_requires_maintenance_congruence_for_interference() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
            slice.interference_removals.len(),
            1,
            "the selected X=Y event automatically makes F(X)=F(Y), so omitting the Parent delete makes replay congruence-collide the stale and recreated rows"
        );

        let mut omitted_creator = EGraph::default();
        serial_causal_pool()
            .install(|| omitted_creator.enable_causal_receipts())
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
            omitted_slice.interference_removals.is_empty(),
            "when the stale constructor source is absent from replay, its delete is correctly unnecessary"
        );
    }

    #[test]
    fn selected_child_delete_prevents_spurious_parent_delete_interference() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
            slice.interference_removals.len(),
            1,
            "the required Leaf delete prevents old/new Leaf outputs from congruence-colliding, so Parent deletion is noninterfering"
        );
        assert_eq!(
            slice.matches.len(),
            2,
            "only recreate and the required Leaf delete should replay"
        );
    }

    #[test]
    fn same_syntax_constructor_recreation_retains_raw_reconciliation() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        assert_eq!(slice.interference_removals.len(), 1);
        assert_eq!(slice.matches.len(), 3, "recreate, reconcile, and delete");
        assert_eq!(slice.equalities.len(), 1);
        let equality = slice.equality_records.values().next().unwrap();
        assert_eq!(equality.left.term, equality.right.term);
        assert_ne!(equality.left.raw, equality.right.raw);
        let replay = crate::causal_replay::build_causal_replay_ir(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_causal_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn duplicate_syntax_in_one_binding_keeps_distinct_occurrence_windows() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        let replay = crate::causal_replay::build_causal_replay_ir(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        let rendered = crate::causal_replay::CausalReplayIr::render_commands(&commands).unwrap();
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
        serial_causal_pool()
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
            serial_causal_pool()
                .install(|| egraph.enable_causal_receipts())
                .unwrap();
            egraph.parse_and_run_program(None, program).unwrap();
            let bridge = egraph
                .backend
                .as_any()
                .downcast_ref::<egglog_bridge::EGraph>()
                .unwrap();
            bridge
                .with_causal_receipt_view(|view| {
                    assert_eq!(view.totals().removals, 1);
                    Ok(())
                })
                .unwrap();
            let slice = slice_all_checks(&egraph).unwrap();
            assert!(slice.interference_removals.is_empty());
            assert!(slice.replay_removals.is_empty());
        }
    }

    #[test]
    fn merge_old_noop_is_retained_only_with_an_effective_sibling() {
        let mut effective_sibling = EGraph::default();
        serial_causal_pool()
            .install(|| effective_sibling.enable_causal_receipts())
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
        assert_eq!(slice.matches.len(), 1);
        let matched = *slice.matches.iter().next().unwrap();
        let bridge = effective_sibling
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        bridge
            .with_causal_receipt_view(|view| {
                let reads = view.matched(matched)?.merge_reads;
                assert_eq!(reads.len(), 1);
                assert!(slice.facts.contains(&reads[0]));
                Ok(())
            })
            .unwrap();

        let mut noop_only = EGraph::default();
        serial_causal_pool()
            .install(|| noop_only.enable_causal_receipts())
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
        assert!(slice.matches.is_empty());
        // The lower-level recorder contract (including zero durable promotion)
        // is covered by `unchanged_merge_without_effective_sibling_promotes_nothing`.
        // Here the frontend contract is that an unrelated check never selects
        // or replays the no-op-only firing.
    }

    #[test]
    fn same_term_child_occurrences_keep_their_native_bridge() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
            Err(CausalSliceError::MissingSupport {
                kind: "applied equality",
                ..
            })
        ));
        let replay = crate::causal_replay::build_causal_replay_ir(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_causal_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn relational_check_shared_variable_equality_is_retained() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        assert_eq!(slice.matches.len(), 1);
        assert_eq!(slice.equalities.len(), 1);
    }

    #[test]
    fn selected_match_exposes_whole_head_without_causal_closing_sibling() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        assert_eq!(slice.matches.len(), 1);
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
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        assert_eq!(slice.matches.len(), 4);
        assert_eq!(slice.interference_removals.len(), 1);
    }

    #[test]
    fn direct_check_retains_nested_child_equality_used_by_a_head_term() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
            slice.matches.len(),
            2,
            "the parent union and nested A/Alias equality are both required"
        );
        let replay = crate::causal_replay::build_causal_replay_ir(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_causal_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn eqsort_result_of_replay_safe_primitive_is_structurally_available() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        assert_eq!(slice.matches.len(), 1);
        let replay = crate::causal_replay::build_causal_replay_ir(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_causal_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn repeated_pure_result_guards_share_one_naming_recipe() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        assert_eq!(slice.matches.len(), 1);
        let replay = crate::causal_replay::build_causal_replay_ir(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_causal_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn eqsort_projection_retains_the_child_equality_it_observed() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        serial_causal_pool()
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
        assert_eq!(slice.matches.len(), 3);
        assert_eq!(slice.equalities.len(), 1);
        let mut damaged = slice.clone();
        damaged.equalities.clear();
        assert!(matches!(
            damaged.validate_exact_support(),
            Err(CausalSliceError::MissingSupport {
                kind: "applied equality",
                ..
            })
        ));
        let replay = crate::causal_replay::build_causal_replay_ir(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled();
        serial_causal_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }

    #[test]
    fn congruence_projection_retains_historical_child_union() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
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
        let replay = crate::causal_replay::build_causal_replay_ir(&egraph, &slice).unwrap();
        let commands = replay.to_commands().unwrap();
        drop(egraph);

        let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
        serial_causal_pool()
            .install(|| proof.run_program(commands))
            .unwrap();
    }
}

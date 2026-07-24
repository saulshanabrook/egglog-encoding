use std::collections::VecDeque;

use crate::core_relations::{
    AppliedEqualityId, CausalReceiptView, CheckEndpointOccurrence, CheckRoot, EqualityEdgeCount,
    EqualityEndpoint, EqualityReason, FactCellRef, FactId, HistoryPosition,
    ProjectedAppliedEquality, RawEqualityEndpoint, RawEqualitySupport, RawReceiptCause,
    ReceiptCausePrior, ReceiptCauseRef, ReceiptEqualitySource, ReceiptViewError, ReplaySortId,
    ReplayTableKind, ReplayTermId, RuleMatchId, SourceRef, TableId, TypedCellEquality, Value,
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
            EqualityReason::MergeFn { cause } | EqualityReason::Congruence { cause, .. } => {
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
            EqualityReason::RuleUnion(_) => continue,
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
        let (table, victim_key) = replay_key_at(view, removal.removed_fact, removal.position)?;
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
        let (table, key) = replay_key_at(view, removal.removed_fact, removal.position)?;
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

    for ((left, right), (left_occurrence, right_occurrence)) in root
        .equalities
        .iter()
        .copied()
        .zip(root.equality_occurrences.iter().copied())
    {
        let left_cell = check_occurrence_cell(left_occurrence);
        let right_cell = check_occurrence_cell(right_occurrence);
        let support = match (left_cell, right_cell) {
            (Some(left), Some(right)) => {
                view.explain_fact_cell_support_at(left, right, root.as_of_edges, root.position)?
            }
            (left_cell, right_cell) => {
                let mut facts = Vec::new();
                let mut rekeys = Vec::new();
                let left = if let Some(cell) = left_cell {
                    let cell = view.fact_cell_at(cell, root.position)?;
                    facts.push(cell.occurrence.fact);
                    rekeys.extend(cell.rekeys);
                    cell.created
                } else {
                    left
                };
                let right = if let Some(cell) = right_cell {
                    let cell = view.fact_cell_at(cell, root.position)?;
                    facts.push(cell.occurrence.fact);
                    rekeys.extend(cell.rekeys);
                    cell.created
                } else {
                    right
                };
                let support =
                    view.explain_equality_support_at(left, right, root.as_of_edges, root.position)?;
                facts.extend(support.facts);
                facts.sort_unstable();
                facts.dedup();
                rekeys.extend(support.rekeys);
                rekeys.sort_unstable();
                rekeys.dedup();
                RawEqualitySupport {
                    applied: support.applied,
                    facts: facts.into_boxed_slice(),
                    causes: support.causes,
                    rekeys: rekeys.into_boxed_slice(),
                }
            }
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
                    slice.match_terms.insert(id, view.match_terms(id)?);
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
                    slice.equality_records.insert(id, event);
                    work.push_back(Work::Cause(match reason {
                        EqualityReason::RuleUnion(rule) => ReceiptCauseRef::Rule(rule),
                        EqualityReason::MergeFn { cause }
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

        let bridge = egraph
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        let before = bridge.causal_compatibility_projection_reads().unwrap();
        let slice = slice_check(&egraph, 0).unwrap();
        let after = bridge.causal_compatibility_projection_reads().unwrap();
        assert_eq!(before, after, "timed slicing constructed no full snapshot");
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
    fn repeated_variable_source_after_equality_never_returns_empty_support() {
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
                 (relation Out (Unit))
                 (rule () ((union (A 1) (B 2))) :name \"eq-ab\")
                 (rule ((R x) (S x)) ((Out ())) :name \"join\")
                 (run 1)
                 (R (A 1))
                 (S (B 2))
                 (run 1)
                 (check (Out ()))",
            )
            .unwrap();

        let error = slice_check(&egraph, 0).unwrap_err();
        assert!(matches!(
            error,
            CausalSliceError::Receipt(ReceiptViewError::Invalid(message))
                if message.contains("requires exact occurrence provenance")
        ));
    }

    #[test]
    fn lowered_nested_constructor_equality_is_retained() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (F i64) (G i64))
                 (relation R (E))
                 (relation Out (Unit))
                 (rule () ((union (F 1) (G 1))) :name \"eq-fg\")
                 (rule ((R (F x))) ((Out ())) :name \"nested\")
                 (F 1)
                 (R (G 1))
                 (run 2)
                 (check (Out ()))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.matches.len(), 2);
        assert_eq!(slice.equalities.len(), 1);
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
    fn selected_source_exposes_all_constructor_effects_of_the_action() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (F E) (G i64))
                 (relation R (E))
                 (R (F (G 1)))
                 (check (R x))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        assert_eq!(slice.sources.len(), 1);
        assert_eq!(slice.facts.len(), 1, "only the checked relation is causal");
        assert!(
            slice.replay_facts.len() >= 3,
            "the selected source action also creates its nested constructors"
        );
    }

    #[test]
    fn future_selected_union_makes_constructor_keys_interfere() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A) (B) (Parent E))
                 (relation Delete (Unit))
                 (relation Recreate (Unit))
                 (relation Before (E))
                 (relation After (E))
                 (rule ((Delete u)) ((delete (Parent (A)))) :name \"delete-parent\")
                 (rule ((Recreate u)) ((After (Parent (B)))) :name \"recreate-parent\")
                 (rule ((Before old) (After new))
                       ((union (A) (B)) (union old new))
                       :name \"reconcile\")
                 (Before (Parent (A)))
                 (Delete ())
                 (run 1)
                 (Recreate ())
                 (run 1)
                 (run 1)
                 (check (Before x) (After x))",
            )
            .unwrap();

        let slice = slice_all_checks(&egraph).unwrap();
        assert_eq!(slice.interference_removals.len(), 1);
        assert_eq!(slice.matches.len(), 3, "recreate, reconcile, and delete");
        assert_eq!(slice.equalities.len(), 1);
        assert_eq!(
            slice.replay_equalities.len(),
            2,
            "the sibling key union is replay-visible but not causal support"
        );
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
    fn raw_equality_view_builds_one_forest_for_many_historical_cutoffs() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A) (B) (C))
                 (relation First (Unit))
                 (relation Second (Unit))
                 (First ())
                 (rule ((First u)) ((union (A) (B))) :name \"first\")
                 (run 1)
                 (Second ())
                 (rule ((Second u)) ((union (B) (C))) :name \"second\")
                 (run 1)
                 (check (= (A) (C)))",
            )
            .unwrap();

        let bridge = egraph
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        bridge
            .with_causal_receipt_view(|view| {
                assert_eq!(view.totals().applied_equalities, 2);
                let first = view.applied_equality(AppliedEqualityId::new(1))?;
                let second = view.applied_equality(AppliedEqualityId::new(2))?;
                assert!(first.position < second.position);
                for _ in 0..16 {
                    assert_eq!(
                        view.explain_raw_equality_support_at(
                            first.left,
                            first.right,
                            EqualityEdgeCount::new(1),
                            first.position,
                        )?
                        .applied
                        .as_ref(),
                        &[AppliedEqualityId::new(1)]
                    );
                    let early = view
                        .explain_raw_equality_support_at(
                            second.left,
                            second.right,
                            EqualityEdgeCount::new(1),
                            first.position,
                        )
                        .unwrap_err();
                    assert!(
                        early
                            .to_string()
                            .contains("disconnected at the historical landmark")
                    );
                    assert_eq!(
                        view.explain_raw_equality_support_at(
                            second.left,
                            second.right,
                            EqualityEdgeCount::new(2),
                            second.position,
                        )?
                        .applied
                        .as_ref(),
                        &[AppliedEqualityId::new(2)]
                    );
                }
                let counters = view.view_counters();
                assert_eq!(counters.equality_index_builds, 1);
                assert_eq!(counters.equality_events_indexed, 2);
                assert_eq!(counters.equality_positions_validated, 2);
                assert_eq!(counters.equality_explanation_queries, 48);
                Ok(())
            })
            .unwrap();
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
                 (rule ((Delete key)) ((delete (Leaf key))) :name \"delete-leaf\")
                 (rule ((Recreate key)) ((After (Leaf key))) :name \"recreate-leaf\")
                 (rule ((Before old) (After new)) ((union old new)) :name \"reconcile\")
                 (Before (Leaf 1))
                 (Delete 1)
                 (run 1)
                 (Recreate 1)
                 (run 1)
                 (run 1)
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
    }

    #[test]
    fn equality_key_identity_includes_raw_occurrence_until_selected_union() {
        let sort = ReplaySortId::new(1);
        let term = ReplayTermId::new(1);
        let old = KeyCell::Equality(TypedTerm {
            sort,
            term,
            raw: Value::new(1),
        });
        let recreated = KeyCell::Equality(TypedTerm {
            sort,
            term,
            raw: Value::new(2),
        });
        let mut dsu = SelectedEqualityDsu::default();
        assert!(!dsu.equivalent(old, recreated));
        let (KeyCell::Equality(old), KeyCell::Equality(recreated)) = (old, recreated) else {
            unreachable!()
        };
        dsu.union(old, recreated);
        assert!(dsu.equivalent(KeyCell::Equality(old), KeyCell::Equality(recreated)));
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
    fn equality_check_after_rekey_uses_root_occurrences_and_matches_snapshot_support() {
        let mut egraph = EGraph::default();
        serial_causal_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))
                 (relation Go (Unit))
                 (let $lhs (A 1))
                 (Go ())
                 (rule ((Go u)) ((union (A 1) (B 2))) :name \"merge\")
                 (run 1)
                 (check (= $lhs (B 2)))",
            )
            .unwrap();

        let slice = slice_check(&egraph, 0).unwrap();
        assert_eq!(slice.matches.len(), 1);
        assert_eq!(slice.equalities.len(), 1);

        let bridge = egraph
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        bridge
            .with_causal_receipt_view(|view| {
                let root = view.check_root(0)?.clone();
                assert_eq!(root.equality_occurrences.len(), 1, "{root:#?}");
                assert!(
                    root.equality_occurrences
                        .iter()
                        .flat_map(|(left, right)| [left, right])
                        .all(|source| !matches!(source, CheckEndpointOccurrence::Current))
                );

                let (left, right) = root.equalities[0];
                let generic =
                    view.explain_equality_support_at(left, right, root.as_of_edges, root.position)?;
                assert_eq!(generic.applied.len(), 1);
                Ok(())
            })
            .unwrap();

        let snapshot = egraph.causal_receipt_snapshot().unwrap();
        let root = &snapshot.check_roots[0];
        let (left, right) = root.equalities[0];
        let support = snapshot
            .explain_equality_support_at(left, right, root.as_of_edges, root.position)
            .unwrap();
        let snapshot_edges = support
            .edges
            .iter()
            .map(|edge| edge.get())
            .collect::<HashSet<_>>();
        let lazy_edges = slice
            .equalities
            .iter()
            .map(|edge| edge.get())
            .collect::<HashSet<_>>();
        assert_eq!(lazy_edges, snapshot_edges);
    }
}

//! Backward dynamic selection over the captured execution history.
//!
//! # Selection laws
//!
//! Selection starts from every recorded successful check and follows the exact
//! historical fact, equality, rekey, cause, and firing dependencies that made
//! those criteria true. All explanations are evaluated at their recorded
//! history position; a later equality cannot justify an earlier read.
//!
//! The result deliberately separates *support* from *replay effects*. Support
//! is the causal cone needed to justify criteria and grounded rule bindings.
//! Once a source command or rule firing enters that cone, replay must expose
//! the owner's complete visible action bundle, including facts, equalities, and
//! removals that were not themselves evidence for the criterion. Equality
//! effects additionally close over the history needed to reproduce the
//! denotation of both endpoints.
//!
//! Finally, selection retains otherwise-unneeded removals when omitting one
//! would leave a stale keyed row able to collide with a later selected row.
//! Owner closure, equality-denotation closure, maintenance equalities, and
//! interference removals are iterated until no new support is discovered.
//!
//! The result is intended to capture one historical support cone. Tests provide
//! regression evidence for that contract; the result is neither a claim of
//! global minimality nor a reconstructed proof.

use std::collections::VecDeque;

use crate::core_relations::{
    AppliedEqualityId, CauseId, CauseRef, Criterion, CriterionEndpointOccurrence, EqualityEndpoint,
    EqualityReason, FactCellRef, FactId, FiringEqualitySource, FiringId, HistoryPosition,
    PremiseOccurrence, ProjectedAppliedEquality, RawCause, RawEqualityEndpoint, RawEqualitySupport,
    ReplayAliasPlan, ReplayTableKind, ReplayTermId, SourceRef, TableId, TraceView, TraceViewError,
    TypedCellEquality, Value,
};
use crate::numeric_id::NumericId;
use crate::util::{HashMap, HashSet};

use crate::EGraph;

#[derive(Default)]
/// The closed selection consumed by replay lowering.
///
/// This contains only the reconstruction set read by replay lowering. The
/// visited sets and projected equality records used while closing the trace
/// remain private to [`SelectionState`].
pub(super) struct Slice {
    /// Removal effects needed by an owner or to prevent stale-row interference.
    pub(super) replay_removals: HashSet<usize>,
    /// Source commands and input rows needed by the selection.
    pub(super) source_roots: HashSet<SourceRef>,
    /// Structural terms paired with checked-alias schedules for each selected firing.
    pub(super) firing_bindings: HashMap<FiringId, Box<[FiringBindingPlan]>>,
}

#[derive(Default)]
/// Mutable closure state discarded once replay's reconstruction set is closed.
struct SelectionState {
    slice: Slice,
    facts: HashSet<FactId>,
    equalities: HashSet<AppliedEqualityId>,
    replay_facts: HashSet<FactId>,
    rekeys: HashSet<HistoryPosition>,
    causes: HashSet<CauseRef>,
    equality_records: HashMap<AppliedEqualityId, ProjectedAppliedEquality>,
}

#[derive(Debug)]
/// One grounded binding term and its child-first checked-alias schedule.
pub(super) struct FiringBindingPlan {
    /// Graph-neutral structural term bound by the firing.
    pub(super) term: ReplayTermId,
    /// Capture bounds aligned with the term's child-first call occurrences.
    pub(super) aliases: Box<[ReplayAliasPlan]>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
/// A source-level unit whose complete visible effects execute together.
///
/// Rule causes belong to their grounded firing and source causes belong to the
/// originating command or input row. Merge causes inherit the incoming owner;
/// rebuild and container-maintenance causes do not manufacture an independent
/// source-level owner.
enum ReplayOwner {
    Firing(FiringId),
    Source(SourceRef),
}

#[derive(Default)]
/// Every trace effect attributed to one replay owner.
///
/// Selecting the owner copies this whole bundle into the replay-effect sets;
/// equality effects also enqueue endpoint-denotation closure.
struct OwnerEffects {
    facts: Vec<FactId>,
    equalities: Vec<AppliedEqualityId>,
    removals: Vec<usize>,
}

type OwnerIndex = HashMap<ReplayOwner, OwnerEffects>;

#[derive(Clone, Copy)]
enum KeyCell {
    Base(Value),
    Equality(EqualityEndpoint),
}

#[derive(Default)]
/// Equality closure visible in the selected replay, used only for key tests.
///
/// Interference analysis must not borrow equalities from the unselected
/// execution, so this disjoint-set contains exactly the projected equality
/// effects in `SelectionState::equality_records`.
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

#[derive(Debug, thiserror::Error)]
/// Failures detected while selecting an internal [`Slice`].
///
/// The public facade does not expose this implementation type; it maps these
/// failures into the crate's existing `crate::Error` result type.
pub(super) enum SliceError {
    #[error(transparent)]
    Trace(#[from] TraceViewError),
    #[error("causal slicing is unavailable without exact trace capture")]
    Disabled,
    #[error("causal slicing requires the concrete main bridge backend")]
    UnsupportedBackend,
    #[error("causal slicing cannot use a poisoned capture: {0}")]
    Poisoned(String),
}

/// One obligation in the mixed-domain backward-closure worklist.
///
/// Keeping equality support and equality denotation as distinct work items
/// lets effect selection separately trigger the history needed to name the
/// equality's endpoints.
enum Work {
    Fact(FactId),
    Firing(FiringId),
    Cause(CauseRef),
    Equality(AppliedEqualityId),
    EqualityDenotation(AppliedEqualityId),
    Rekey(HistoryPosition),
}

/// Add one sufficient historical explanation to the closure worklist.
fn enqueue_support(work: &mut VecDeque<Work>, support: RawEqualitySupport) {
    for id in &support.applied {
        work.push_back(Work::Equality(*id));
    }
    for id in &support.facts {
        work.push_back(Work::Fact(*id));
    }
    for position in &support.rekeys {
        work.push_back(Work::Rekey(*position));
    }
}

fn check_occurrence_cell(occurrence: CriterionEndpointOccurrence) -> Option<FactCellRef> {
    match occurrence {
        CriterionEndpointOccurrence::FactCell(cell) => Some(cell),
        CriterionEndpointOccurrence::Current => None,
    }
}

/// Explain a grounded rule equality at the firing's recorded landmark.
///
/// Premise occurrences retain their fact-cell provenance; constants are
/// resolved as typed equality endpoints. Rekeys encountered while recovering
/// either spelling become support obligations as well.
fn explain_rule_equality(
    view: &mut TraceView<'_>,
    left: FiringEqualitySource,
    right: FiringEqualitySource,
    premises: &[FactId],
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
        (FiringEqualitySource::Premise(left), FiringEqualitySource::Premise(right)) => {
            view.explain_fact_cell_support_at(premise_cell(left)?, premise_cell(right)?, position)
        }
        (FiringEqualitySource::Premise(fact), FiringEqualitySource::Constant(endpoint))
        | (FiringEqualitySource::Constant(endpoint), FiringEqualitySource::Premise(fact)) => {
            view.explain_fact_endpoint_support_at(premise_cell(fact)?, endpoint, position)
        }
        (FiringEqualitySource::Constant(left), FiringEqualitySource::Constant(right)) => {
            view.explain_equality_support_at(left, right, position)
        }
    }
}

/// Resolve a trace cause to the source-level owner whose action emitted it.
///
/// The recursion follows merge provenance and rejects cause cycles. Native
/// maintenance remains ownerless because its replay visibility is derived from
/// the selected source-level effects that trigger it.
fn replay_owner_for_cause(
    view: &TraceView<'_>,
    cause: CauseRef,
    memo: &mut HashMap<CauseId, Option<ReplayOwner>>,
    active: &mut HashSet<CauseId>,
) -> Result<Option<ReplayOwner>, TraceViewError> {
    let id = match cause {
        CauseRef::Rule(rule) => return Ok(Some(ReplayOwner::Firing(rule))),
        CauseRef::Cause(id) => id,
    };
    if let Some(owner) = memo.get(&id) {
        return Ok(owner.clone());
    }
    if !active.insert(id) {
        return Err(TraceViewError::Invalid(format!(
            "trace cause cycle reaches {cause:?}"
        )));
    }
    let owner = match view.cause(id)? {
        RawCause::Source(source) => Some(ReplayOwner::Source(source.clone())),
        RawCause::Merge { incoming, .. } => replay_owner_for_cause(view, incoming, memo, active)?,
        RawCause::Rebuild { .. }
        | RawCause::ContainerCanonicalize { .. }
        | RawCause::ContainerRefresh { .. } => None,
    };
    active.remove(&id);
    memo.insert(id, owner.clone());
    Ok(owner)
}

/// Index the complete fact, equality, and removal bundle of every replay owner.
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

/// Select an equality effect and enqueue closure of its endpoint denotations.
fn mark_replay_equality(
    view: &mut TraceView<'_>,
    selection: &mut SelectionState,
    work: &mut VecDeque<Work>,
    id: AppliedEqualityId,
) -> Result<(), TraceViewError> {
    if !selection.equality_records.contains_key(&id) {
        let event = view.project_applied_equality(id)?;
        selection.equality_records.insert(id, event);
        work.push_back(Work::EqualityDenotation(id));
    }
    Ok(())
}

/// Copy all effects of a selected owner into the replay-effect sets.
///
/// This is the boundary between causal support and action semantics: selecting
/// one consequence of a source command or firing means replaying its other
/// visible consequences too.
fn mark_owner_visible(
    view: &mut TraceView<'_>,
    index: &OwnerIndex,
    selection: &mut SelectionState,
    work: &mut VecDeque<Work>,
    owner: &ReplayOwner,
) -> Result<(), TraceViewError> {
    let Some(effects) = index.get(owner) else {
        return Ok(());
    };
    selection.replay_facts.extend(effects.facts.iter().copied());
    for id in effects.equalities.iter().copied() {
        mark_replay_equality(view, selection, work, id)?;
    }
    selection
        .slice
        .replay_removals
        .extend(effects.removals.iter().copied());
    Ok(())
}

/// Build the equality relation that the generated replay will actually see.
fn selected_equality_dsu(selection: &SelectionState) -> SelectedEqualityDsu {
    let mut dsu = SelectedEqualityDsu::default();
    for event in selection.equality_records.values() {
        dsu.union(event.left, event.right);
    }
    dsu
}

/// Test whether every equality landmark is derivable from selected effects.
fn equality_landmark_is_replay_visible(
    view: &mut TraceView<'_>,
    selection: &SelectionState,
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
            position,
        )?;
        if support
            .applied
            .iter()
            .any(|edge| !selection.equality_records.contains_key(edge))
        {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Test whether a native maintenance cause follows from already-selected state.
///
/// Maintenance landmarks are historical cutoffs. Every equality they consult
/// must precede the event being considered and already belong to the replay
/// equality relation.
fn maintenance_cause_is_replay_visible(
    view: &mut TraceView<'_>,
    selection: &SelectionState,
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
        CauseRef::Rule(rule) => selection.slice.firing_bindings.contains_key(&rule),
        CauseRef::Cause(id) => match view.cause(id)? {
            RawCause::Source(source) => selection.slice.source_roots.contains(source),
            RawCause::Merge {
                incoming,
                prior_fact,
            } => {
                let incoming = maintenance_cause_is_replay_visible(
                    view,
                    selection,
                    incoming,
                    current_event,
                    active,
                )?;
                let prior = selection.replay_facts.contains(&prior_fact);
                incoming && prior
            }
            RawCause::Rebuild {
                prior_fact,
                position,
                equalities,
                ..
            }
            | RawCause::ContainerRefresh {
                prior_fact,
                position,
                equalities,
                ..
            } => {
                if position >= view.applied_equality(current_event)?.position {
                    return Err(TraceViewError::Invalid(format!(
                        "maintenance equality {current_event:?} depends on a non-earlier history landmark {position:?}"
                    )));
                }
                selection.replay_facts.contains(&prior_fact)
                    && equality_landmark_is_replay_visible(view, selection, position, equalities)?
            }
            RawCause::ContainerCanonicalize {
                position,
                equalities,
                ..
            } => {
                if position >= view.applied_equality(current_event)?.position {
                    return Err(TraceViewError::Invalid(format!(
                        "maintenance equality {current_event:?} depends on a non-earlier history landmark {position:?}"
                    )));
                }
                equality_landmark_is_replay_visible(view, selection, position, equalities)?
            }
        },
    };
    active.remove(&cause);
    Ok(visible)
}

/// Retain implicit merge/congruence equalities implied by replay-visible state.
///
/// This extra pass is needed only for non-monotone traces. Applied equality ids
/// follow execution chronology, and every maintenance event cites only earlier
/// landmarks. Owner-selected equalities are already present, so a single
/// forward scan is sufficient and avoids a quadratic fixpoint over a dense
/// equality log.
fn select_replay_maintenance_equalities(
    view: &mut TraceView<'_>,
    selection: &mut SelectionState,
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
        if selection.equality_records.contains_key(&id) {
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
        if !maintenance_cause_is_replay_visible(view, selection, cause, id, &mut active)? {
            continue;
        }
        mark_replay_equality(view, selection, work, id)?;
        selected_any = true;
    }
    Ok(selected_any)
}

/// Project a fact's keyed columns as they were addressable at `position`.
///
/// Equality-sort columns become typed endpoints compared through the selected
/// equality relation; base-sort columns retain their exact values.
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

/// Retain deletions whose omission could change a later selected insertion.
///
/// For each unselected removal of a replay-visible keyed fact, this compares
/// the victim's pre-removal key with later replay facts in the same table using
/// only selected equalities. A collision keeps both the removal and its owning
/// firing, preventing a stale row from absorbing or merging with the later row.
/// Presence relations are monotone for this purpose and need no such deletion.
fn select_interfering_removals(
    view: &mut TraceView<'_>,
    selection: &mut SelectionState,
    work: &mut VecDeque<Work>,
) -> Result<bool, TraceViewError> {
    if view.totals().removals == 0 {
        return Ok(false);
    }
    let mut dsu = selected_equality_dsu(selection);
    let replay_facts = selection.replay_facts.iter().copied().collect::<Vec<_>>();
    let mut selected_any = false;
    for index in 0..view.totals().removals as usize {
        if selection.slice.replay_removals.contains(&index) {
            continue;
        }
        let removal = view.removal(index)?.clone();
        if !selection.replay_facts.contains(&removal.removed_fact) {
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
            selection.slice.replay_removals.insert(index);
            work.push_back(Work::Firing(removal.cause));
            selected_any = true;
        }
    }
    Ok(selected_any)
}

/// Seed one successful check with its premises and exact equality support.
///
/// Endpoint-occurrence metadata is preserved so selection includes both the
/// equality evidence and the historical support that made each recorded
/// endpoint spelling available at the check.
fn seed_check_root(
    view: &mut TraceView<'_>,
    work: &mut VecDeque<Work>,
    root: &Criterion,
) -> Result<(), TraceViewError> {
    work.extend(root.premises.iter().copied().map(Work::Fact));

    for equality in root.equalities.iter().copied() {
        let ((left_endpoint, right_endpoint), (left_occurrence, right_occurrence)) =
            (equality.endpoints, equality.occurrences);
        let left_cell = check_occurrence_cell(left_occurrence);
        let right_cell = check_occurrence_cell(right_occurrence);
        let support = match (left_cell, right_cell) {
            (Some(left), Some(right)) => {
                let exact = view.explain_fact_cell_support_at(left, right, root.position)?;
                enqueue_support(work, exact);
                let left_source =
                    view.explain_fact_endpoint_availability_at(left, left_endpoint, root.position)?;
                enqueue_support(work, left_source.support);
                view.explain_fact_endpoint_availability_at(right, right_endpoint, root.position)?
                    .support
            }
            (Some(fact), None) => {
                let source =
                    view.explain_fact_endpoint_availability_at(fact, left_endpoint, root.position)?;
                enqueue_support(work, source.support);
                view.explain_fact_endpoint_support_at(fact, right_endpoint, root.position)?
            }
            (None, Some(fact)) => {
                let source = view.explain_fact_endpoint_availability_at(
                    fact,
                    right_endpoint,
                    root.position,
                )?;
                enqueue_support(work, source.support);
                view.explain_fact_endpoint_support_at(fact, left_endpoint, root.position)?
            }
            (None, None) => {
                view.explain_equality_support_at(left_endpoint, right_endpoint, root.position)?
            }
        };
        enqueue_support(work, support);
    }
    Ok(())
}

/// Close successful criteria over causal support and replay-visible effects.
///
/// The inner worklist follows facts, firings, causes, equalities, endpoint
/// denotations, and rekeys. After it drains, native maintenance equalities and
/// interference removals may introduce new obligations; the outer loop repeats
/// until both passes are stable, then validates every saved exact explanation.
fn slice_roots(view: &mut TraceView<'_>, roots: Vec<Criterion>) -> Result<Slice, TraceViewError> {
    let owner_index = build_owner_index(view)?;
    let mut selection = SelectionState::default();
    let mut work = VecDeque::new();
    for root in &roots {
        seed_check_root(view, &mut work, root)?;
    }

    loop {
        while let Some(item) = work.pop_front() {
            match item {
                Work::Fact(id) => {
                    if !selection.facts.insert(id) {
                        continue;
                    }
                    selection.replay_facts.insert(id);
                    let cause = view.fact(id)?.cause;
                    work.push_back(Work::Cause(cause));
                }
                Work::Firing(id) => {
                    if selection.slice.firing_bindings.contains_key(&id) {
                        continue;
                    }
                    mark_owner_visible(
                        view,
                        &owner_index,
                        &mut selection,
                        &mut work,
                        &ReplayOwner::Firing(id),
                    )?;
                    let firing = view.firing(id)?;
                    let rule = firing.rule;
                    let position = firing.position;
                    let premises = firing.premises.to_vec();
                    let merge_reads = firing.merge_reads.to_vec();
                    work.extend(premises.iter().copied().map(Work::Fact));
                    work.extend(merge_reads.into_iter().map(Work::Fact));
                    let terms = view.firing_terms(id)?;
                    let mut bindings = Vec::with_capacity(terms.len());
                    for (binding, term) in terms.iter().copied().enumerate() {
                        let availability = view.explain_firing_term_availability(id, binding)?;
                        enqueue_support(&mut work, availability.support);
                        bindings.push(FiringBindingPlan {
                            term,
                            aliases: availability.aliases,
                        });
                    }
                    selection
                        .slice
                        .firing_bindings
                        .insert(id, bindings.into_boxed_slice());
                    for (left, right) in view.rule_equality_layout(rule)?.iter().copied() {
                        let support =
                            explain_rule_equality(view, left, right, &premises, position)?;
                        enqueue_support(&mut work, support);
                    }
                }
                Work::Cause(cause) => {
                    if !selection.causes.insert(cause) {
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
                            selection.slice.source_roots.insert(source.clone());
                            mark_owner_visible(
                                view,
                                &owner_index,
                                &mut selection,
                                &mut work,
                                &ReplayOwner::Source(source),
                            )?;
                        }
                        RawCause::Rebuild {
                            prior_fact,
                            position,
                            equalities,
                            ..
                        }
                        | RawCause::ContainerRefresh {
                            prior_fact,
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
                                    position,
                                )?;
                                enqueue_support(&mut work, support);
                            }
                        }
                        RawCause::ContainerCanonicalize {
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
                                    position,
                                )?;
                                enqueue_support(&mut work, support);
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
                    if !selection.equalities.insert(id) {
                        continue;
                    }
                    mark_replay_equality(view, &mut selection, &mut work, id)?;
                    let event = selection
                        .equality_records
                        .get(&id)
                        .expect("selected equality lost its projected record")
                        .clone();
                    let reason = event.reason.clone();
                    if let EqualityReason::Congruence { position, .. } = reason {
                        let support = view.explain_congruence_child_support_at(
                            event.left,
                            event.right,
                            position,
                        )?;
                        enqueue_support(&mut work, support);
                    }
                    work.push_back(Work::Cause(match reason {
                        EqualityReason::RuleUnion(rule) => CauseRef::Rule(rule),
                        EqualityReason::SourceUnion { cause }
                        | EqualityReason::MergeFn { cause }
                        | EqualityReason::Congruence { cause, .. } => CauseRef::Cause(cause),
                    }));
                }
                Work::EqualityDenotation(id) => {
                    let support = view.explain_equality_denotation_before(id)?;
                    enqueue_support(&mut work, support);
                }
                Work::Rekey(position) => {
                    if !selection.rekeys.insert(position) {
                        continue;
                    }
                    let rekey = view.rekey_at(position)?;
                    let fact = rekey.fact;
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
                            equality_position,
                        )?;
                        enqueue_support(&mut work, support);
                    }
                }
            }
        }
        select_replay_maintenance_equalities(view, &mut selection, &mut work)?;
        let selected_removal = select_interfering_removals(view, &mut selection, &mut work)?;
        if work.is_empty() && !selected_removal {
            break;
        }
    }
    Ok(selection.slice)
}

/// Select the union of the support cones for all recorded successful checks.
fn slice_all_view(view: &mut TraceView<'_>) -> Result<Slice, TraceViewError> {
    let roots = view.check_roots().into_iter().cloned().collect();
    slice_roots(view, roots)
}

/// Select all successful checks from a healthy concrete-backend capture.
///
/// This frontend boundary rejects missing or poisoned capture catalogs and
/// non-native backends before borrowing a trace view. The public facade maps
/// the resulting [`SliceError`] into `crate::Error`.
pub(super) fn select_all_checks(egraph: &EGraph) -> Result<Slice, SliceError> {
    egraph
        .capture_catalog
        .as_ref()
        .ok_or(SliceError::Disabled)?
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

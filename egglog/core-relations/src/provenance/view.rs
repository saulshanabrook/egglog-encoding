//! Borrowed historical views over one finalized trace.

use super::*;

#[path = "explain.rs"]
mod explain;

/// Lazy receipt-view projector. Native capture stores raw creation rows and
/// compact static origin sites; selected reads expand only the requested
/// references into the historical replay-term DAG.
#[derive(Clone)]
enum TemplateOwner {
    Durable(RuleMatchId),
    Fact(FactId),
    History {
        position: HistoryPosition,
        inclusive: bool,
    },
}

pub(super) struct TermProjector<'a> {
    arena: &'a ReceiptArena,
    binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
    term_recipes: &'a StaticTermRecipeStore,
    replay_terms: &'a ReplayTermStore,
    next_term: &'a AtomicU32,
    fact_memo: HashMap<(FactId, usize), ReplayTermId>,
    match_memo: HashMap<(RuleMatchId, usize), ReplayTermId>,
    visiting_facts: HashSet<(FactId, usize)>,
    visiting_matches: HashSet<(RuleMatchId, usize)>,
}

impl<'a> TermProjector<'a> {
    pub(super) fn new(
        arena: &'a ReceiptArena,
        binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
        term_recipes: &'a StaticTermRecipeStore,
        replay_terms: &'a ReplayTermStore,
        next_term: &'a AtomicU32,
    ) -> Self {
        Self {
            arena,
            binding_recipes,
            term_recipes,
            replay_terms,
            next_term,
            fact_memo: HashMap::default(),
            match_memo: HashMap::default(),
            visiting_facts: HashSet::default(),
            visiting_matches: HashSet::default(),
        }
    }

    pub(super) fn fact_term(
        &mut self,
        fact_id: FactId,
        column: usize,
    ) -> Result<ReplayTermId, String> {
        if let Some(term) = self.fact_memo.get(&(fact_id, column)).copied() {
            return Ok(term);
        }
        #[cfg(test)]
        TERM_PROJECTOR_FACT_EXPANSIONS.set(TERM_PROJECTOR_FACT_EXPANSIONS.get() + 1);
        if !self.visiting_facts.insert((fact_id, column)) {
            return Err(format!(
                "cyclic causal term origin at {fact_id:?} column {column}"
            ));
        }
        let result = (|| {
            let fact = self
                .arena
                .facts
                .get((fact_id.get().checked_sub(1).ok_or("missing FactId")?) as usize)
                .and_then(Option::as_ref)
                .ok_or_else(|| format!("unknown causal fact {fact_id:?}"))?;
            let owner = self
                .arena
                .originating_rule(fact.cause)
                .map(TemplateOwner::Durable)
                .unwrap_or(TemplateOwner::Fact(fact_id));
            let merge_cells = match fact.origin {
                Some(FactOrigin::Merge { cells, .. }) => {
                    Some(self.arena.durable_merge_cell_origins[cells.as_range()].to_vec())
                }
                _ => None,
            };
            let (table, origin) = (fact.table, fact.origin);
            match origin {
                Some(FactOrigin::Site(site)) => self.site_term(site, table, column, Some(&owner)),
                Some(FactOrigin::Fact(source)) => self.fact_term(source, column),
                Some(FactOrigin::Merge {
                    incoming, prior, ..
                }) => {
                    let cell = *merge_cells
                        .as_deref()
                        .and_then(|cells| cells.get(column))
                        .ok_or_else(|| {
                            format!("merge origin for {fact_id:?} has no column {column}")
                        })?;
                    let incoming_term = |this: &mut Self| match incoming {
                        Some(RowOriginRef::Site(site)) => {
                            this.site_term(site, table, column, Some(&owner))
                        }
                        Some(RowOriginRef::Fact(source)) => this.fact_term(source, column),
                        None => Err(format!(
                            "reached unattributed incoming syntax for {fact_id:?} column {column}"
                        )),
                    };
                    match cell {
                        MergeCellOrigin::Incoming(source) => match incoming {
                            Some(RowOriginRef::Site(site)) => {
                                self.site_term(site, table, source as usize, Some(&owner))
                            }
                            Some(RowOriginRef::Fact(source_fact)) => {
                                self.fact_term(source_fact, source as usize)
                            }
                            None => incoming_term(self),
                        },
                        MergeCellOrigin::Prior(source) => self.fact_term(prior, source as usize),
                        MergeCellOrigin::Unsupported => Err(format!(
                            "merge of {fact_id:?} column {column} synthesized unsupported syntax"
                        )),
                    }
                }
                None => Err(format!(
                    "causal fact {fact_id:?} column {column} has no structural origin"
                )),
            }
        })();
        self.visiting_facts.remove(&(fact_id, column));
        let term = result?;
        self.fact_memo.insert((fact_id, column), term);
        Ok(term)
    }

    fn site_term(
        &mut self,
        site: RowOriginSiteId,
        table: TableId,
        column: usize,
        owner: Option<&TemplateOwner>,
    ) -> Result<ReplayTermId, String> {
        let spec = self
            .term_recipes
            .row_origins
            .get((site.get() - 1) as usize)
            .ok_or_else(|| format!("unknown row-origin site {site:?}"))?;
        if spec.table != table {
            return Err(format!(
                "row-origin site {site:?} belongs to {:?}, not {table:?}",
                spec.table
            ));
        }
        let template = spec
            .cells
            .get(column)
            .and_then(Option::as_ref)
            .ok_or_else(|| {
                format!("reached unsupported causal row origin {site:?} column {column}")
            })?;
        self.template(template, owner)
    }

    fn match_term(
        &mut self,
        match_id: RuleMatchId,
        binding: usize,
    ) -> Result<ReplayTermId, String> {
        if let Some(term) = self.match_memo.get(&(match_id, binding)).copied() {
            return Ok(term);
        }
        if !self.visiting_matches.insert((match_id, binding)) {
            return Err(format!(
                "cyclic causal match term at {match_id:?} binding {binding}"
            ));
        }
        let result = (|| {
            let record = self
                .arena
                .durable_matches
                .get((match_id.get().checked_sub(1).ok_or("missing RuleMatchId")?) as usize)
                .and_then(Option::as_ref)
                .ok_or_else(|| format!("unknown causal match {match_id:?}"))?;
            let rule = record.rule;
            let premises: Arc<[FactId]> =
                self.arena.durable_premises[record.premises.as_range()].into();
            self.binding_term(rule, &premises, binding, &TemplateOwner::Durable(match_id))
        })();
        self.visiting_matches.remove(&(match_id, binding));
        let term = result?;
        self.match_memo.insert((match_id, binding), term);
        Ok(term)
    }

    fn binding_term(
        &mut self,
        rule: u32,
        premises: &[FactId],
        binding: usize,
        owner: &TemplateOwner,
    ) -> Result<ReplayTermId, String> {
        let sources = self
            .binding_recipes
            .get(&rule)
            .ok_or_else(|| format!("rule {rule} has no binding recipe"))?;
        let source = sources
            .get(binding)
            .ok_or_else(|| format!("rule {rule} has no binding slot {binding}"))?;
        match source {
            ReplayBindingSource::Premise { representative, .. } => {
                let fact = *premises.get(representative.premise).ok_or_else(|| {
                    format!(
                        "rule {rule} match has no premise {}",
                        representative.premise
                    )
                })?;
                self.fact_term(fact, representative.column)
            }
            ReplayBindingSource::Constant { term } => Ok(*term),
            ReplayBindingSource::Current { residual, .. } => {
                let recipe = self
                    .term_recipes
                    .rules
                    .get(&rule)
                    .ok_or_else(|| format!("rule {rule} has no current-term recipe"))?;
                let template = recipe
                    .current_roots
                    .get(*residual as usize)
                    .and_then(Option::as_ref)
                    .ok_or_else(|| {
                        format!("reached unsupported current binding {residual} for rule {rule}")
                    })?;
                self.template(template, Some(owner))
            }
        }
    }

    fn template(
        &mut self,
        template: &TermTemplate,
        owner: Option<&TemplateOwner>,
    ) -> Result<ReplayTermId, String> {
        match template {
            TermTemplate::Binding { binding } => match owner.ok_or_else(|| {
                format!("source row origin unexpectedly references binding {binding}")
            })? {
                TemplateOwner::Durable(match_id) => self.match_term(*match_id, *binding as usize),
                TemplateOwner::Fact(fact) => Err(format!(
                    "source fact {fact:?} unexpectedly references binding {binding}"
                )),
                TemplateOwner::History { .. } => Err(format!(
                    "historical term origin unexpectedly references binding {binding}"
                )),
            },
            TermTemplate::PremiseCell { premise, column } => {
                let owner = owner.ok_or_else(|| {
                    format!(
                        "source row origin unexpectedly references premise {premise} column {column}"
                    )
                })?;
                let fact = match owner {
                    TemplateOwner::Durable(match_id) => {
                        let record = self
                            .arena
                            .durable_matches
                            .get(
                                (match_id.get().checked_sub(1).ok_or("missing RuleMatchId")?)
                                    as usize,
                            )
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown causal match {match_id:?}"))?;
                        *self
                            .arena
                            .durable_premises
                            .get(record.premises.as_range())
                            .and_then(|premises| premises.get(*premise as usize))
                            .ok_or_else(|| {
                                format!("causal match {match_id:?} has no premise {premise}")
                            })?
                    }
                    TemplateOwner::Fact(fact) => {
                        return Err(format!(
                            "source fact {fact:?} unexpectedly references premise {premise} column {column}"
                        ));
                    }
                    TemplateOwner::History { .. } => {
                        return Err(format!(
                            "historical term origin unexpectedly references premise {premise} column {column}"
                        ));
                    }
                };
                self.fact_term(fact, *column as usize)
            }
            TermTemplate::Static { term } => Ok(*term),
            TermTemplate::FactLookup { table, column } => {
                let (position, inclusive) = match owner
                    .ok_or_else(|| format!("historical lookup of {table:?} has no owning event"))?
                {
                    TemplateOwner::Durable(match_id) => (
                        self.arena
                            .durable_matches
                            .get(
                                (match_id.get().checked_sub(1).ok_or("missing RuleMatchId")?)
                                    as usize,
                            )
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown causal match {match_id:?}"))?
                            .position,
                        true,
                    ),
                    TemplateOwner::Fact(fact) => (
                        self.arena
                            .facts
                            .get((fact.get().checked_sub(1).ok_or("missing FactId")?) as usize)
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown causal fact {fact:?}"))?
                            .position,
                        false,
                    ),
                    TemplateOwner::History {
                        position,
                        inclusive,
                    } => (*position, *inclusive),
                };
                let (fact, _) = self
                    .arena
                    .facts
                    .iter()
                    .enumerate()
                    .filter_map(|(index, slot)| {
                        let candidate = slot.as_ref()?;
                        let visible = if inclusive {
                            candidate.position <= position
                        } else {
                            candidate.position < position
                        };
                        (candidate.table == *table && visible)
                            .then_some((FactId::new(index as u64 + 1), candidate.position))
                    })
                    .filter(|(fact, _)| {
                        !self.arena.removals.iter().any(|removal| {
                            removal.removed_fact == *fact && removal.position <= position
                        }) && !self.arena.rekeys.iter().any(|rekey| {
                            rekey.fact == *fact
                                && rekey.position <= position
                                && rekey.outcome != RekeyOutcome::Moved
                        })
                    })
                    .max_by_key(|(_, fact_position)| *fact_position)
                    .ok_or_else(|| {
                        format!(
                            "zero-key historical lookup of {table:?} has no live fact at {position:?}"
                        )
                    })?;
                self.fact_term(fact, *column as usize)
            }
            TermTemplate::Call { sort, op, children } => {
                let children = children
                    .iter()
                    .map(|child| self.template(child, owner))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.replay_terms.intern(
                    self.next_term,
                    ReplayTerm::Call {
                        sort: *sort,
                        op: *op,
                        children: children.into(),
                    },
                ))
            }
        }
    }

    pub(super) fn runtime_anchor_template(
        &mut self,
        template: &TermTemplate,
        binding_sources: &[ReplayBindingSource],
        premises: &[FactId],
    ) -> Result<ReplayTermId, String> {
        match template {
            TermTemplate::Binding { binding } => {
                let source = binding_sources.get(*binding as usize).ok_or_else(|| {
                    format!("container anchor references unknown binding {binding}")
                })?;
                match source {
                    ReplayBindingSource::Premise { representative, .. } => {
                        let fact = *premises.get(representative.premise).ok_or_else(|| {
                            format!(
                                "container anchor binding {binding} has no premise {}",
                                representative.premise
                            )
                        })?;
                        self.fact_term(fact, representative.column)
                    }
                    ReplayBindingSource::Constant { term } => Ok(*term),
                    ReplayBindingSource::Current { residual, .. } => Err(format!(
                        "container anchor reached unsupported current binding {binding} (residual {residual})"
                    )),
                }
            }
            TermTemplate::PremiseCell { premise, column } => {
                let fact = *premises
                    .get(*premise as usize)
                    .ok_or_else(|| format!("container anchor has no premise {premise}"))?;
                self.fact_term(fact, *column as usize)
            }
            TermTemplate::Static { term } => Ok(*term),
            TermTemplate::FactLookup { table, .. } => Err(format!(
                "container runtime anchor unexpectedly references zero-key table {table:?}"
            )),
            TermTemplate::Call { sort, op, children } => {
                let children = children
                    .iter()
                    .map(|child| self.runtime_anchor_template(child, binding_sources, premises))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.replay_terms.intern(
                    self.next_term,
                    ReplayTerm::Call {
                        sort: *sort,
                        op: *op,
                        children: children.into(),
                    },
                ))
            }
        }
    }

    fn equality_endpoint(
        &mut self,
        endpoint: PendingEqualityEndpoint,
        cause: CauseRef,
        position: HistoryPosition,
    ) -> Result<EqualityEndpoint, String> {
        let term = match endpoint.term {
            EqualityTermRef::Exact(term) => term,
            EqualityTermRef::Site(site) => {
                let owner = self
                    .arena
                    .originating_rule(cause)
                    .map(TemplateOwner::Durable)
                    .unwrap_or(TemplateOwner::History {
                        position,
                        inclusive: true,
                    });
                let spec = self
                    .term_recipes
                    .term_origins
                    .get((site.get() - 1) as usize)
                    .ok_or_else(|| format!("unknown term-origin site {site:?}"))?;
                if spec.sort != endpoint.sort {
                    return Err(format!(
                        "term-origin site {site:?} belongs to {:?}, not {:?}",
                        spec.sort, endpoint.sort
                    ));
                }
                self.template(&spec.term, Some(&owner))?
            }
            EqualityTermRef::Cell {
                origin,
                table,
                column,
            } => match origin {
                RowOriginRef::Fact(fact) => {
                    let (fact_table, values) = self
                        .arena
                        .fact_values(fact)
                        .ok_or_else(|| format!("unknown equality endpoint fact {fact:?}"))?;
                    if fact_table != table {
                        return Err(format!(
                            "equality endpoint fact {fact:?} belongs to {fact_table:?}, not {table:?}"
                        ));
                    }
                    values.get(column as usize).ok_or_else(|| {
                        format!("equality endpoint fact {fact:?} has no column {column}")
                    })?;
                    self.fact_term(fact, column as usize)?
                }
                RowOriginRef::Site(site) => {
                    let owner = self
                        .arena
                        .originating_rule(cause)
                        .map(TemplateOwner::Durable)
                        .unwrap_or(TemplateOwner::History {
                            position,
                            inclusive: true,
                        });
                    self.site_term(site, table, column as usize, Some(&owner))?
                }
            },
        };
        let node = self
            .replay_terms
            .node(term)
            .ok_or_else(|| format!("equality endpoint owns unknown term {term:?}"))?;
        if node.sort() != endpoint.sort {
            return Err(format!(
                "equality endpoint term sort {:?} differs from {:?}",
                node.sort(),
                endpoint.sort
            ));
        }
        Ok(EqualityEndpoint {
            sort: endpoint.sort,
            term,
            raw: endpoint.raw,
        })
    }
}

/// Borrowed, non-escaping view of one finalized raw receipt arena.
///
/// Accessors project structural terms only for explicitly selected facts,
/// matches, or equality events.
pub struct CausalReceiptView<'a> {
    pub(super) arena: &'a ReceiptArena,
    pub(super) binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
    pub(super) equality_recipes:
        &'a HashMap<u32, Arc<[(ReplayEqualitySource, ReplayEqualitySource)]>>,
    pub(super) term_recipes: &'a StaticTermRecipeStore,
    pub(super) replay_terms: &'a ReplayTermStore,
    pub(super) projector: TermProjector<'a>,
    pub(super) history_boundary: HistoryPosition,
    pub(super) equality_index: Option<RawEqualityIndex>,
    pub(super) rekey_index: Option<RekeyIndex>,
    pub(super) constructor_occurrence_index: Option<ConstructorOccurrenceIndex>,
    pub(super) occurrence_support_cache:
        HashMap<StructuralOccurrenceQuery, Option<RawEqualitySupport>>,
    pub(super) exact_occurrence_support_cache:
        HashMap<StructuralOccurrenceQuery, Option<RawEqualitySupport>>,
    pub(super) counters: CausalReceiptViewCounters,
}

pub(super) struct RawEqualityIndex {
    parents: HashMap<(ReplaySortId, Value), (Value, AppliedEqualityId)>,
}

pub(super) struct RekeyIndex {
    by_fact: HashMap<FactId, Arc<[usize]>>,
    by_position: HashMap<HistoryPosition, usize>,
}

pub(super) struct ConstructorOccurrenceIndex {
    facts: HashMap<(ReplaySortId, ReplayOpId), Arc<[FactId]>>,
    registered: HashSet<(ReplaySortId, ReplayOpId)>,
    /// Non-table calls that were emitted by a frontend-certified static term
    /// recipe. Only these calls may be recomputed by `let-check` without a
    /// constructor FactId. Building this set is deliberately cold: receipt
    /// capture never walks term recipes.
    certified_calls: HashSet<(ReplaySortId, ReplayOpId)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct StructuralOccurrenceQuery {
    term: ReplayTermId,
    sort: ReplaySortId,
    raw: Value,
    position: HistoryPosition,
    excluded_fact: FactId,
}

#[derive(Clone, Copy)]
struct StructuralAvailabilityContext<'a> {
    desired: Option<RawEqualityEndpoint>,
    anchor: Option<&'a HistoricalFactCell>,
    fresh_after: Option<HistoryPosition>,
}

enum ObservedEqualitySupport {
    Support(RawEqualitySupport),
    Missing(ReplayTermId),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CausalReceiptViewCounters {
    pub equality_index_builds: u64,
    pub equality_events_indexed: u64,
    pub equality_positions_validated: u64,
    pub equality_explanation_queries: u64,
    pub equality_parent_steps: u64,
    pub equality_occurrence_facts_scanned: u64,
    pub equality_occurrence_terms_projected: u64,
    pub rekey_lookups: u64,
    pub rekey_records_scanned: u64,
}

impl<'a> CausalReceiptView<'a> {
    fn collect_certified_replay_term_calls(
        &self,
        term: ReplayTermId,
        calls: &mut HashSet<(ReplaySortId, ReplayOpId)>,
        visited: &mut HashSet<ReplayTermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        let Some(node) = self.replay_terms.node(term) else {
            // A malformed static reference certifies nothing. If it is ever
            // reached, ordinary term projection reports the unknown id; an
            // unrelated malformed recipe remains lazy and harmless.
            return;
        };
        let ReplayTerm::Call { sort, op, children } = node else {
            return;
        };
        calls.insert((sort, op));
        for child in children.iter().copied() {
            self.collect_certified_replay_term_calls(child, calls, visited);
        }
    }

    fn collect_certified_template_calls(
        &self,
        template: &TermTemplate,
        calls: &mut HashSet<(ReplaySortId, ReplayOpId)>,
        visited_terms: &mut HashSet<ReplayTermId>,
    ) {
        match template {
            TermTemplate::Binding { .. }
            | TermTemplate::PremiseCell { .. }
            | TermTemplate::FactLookup { .. } => {}
            TermTemplate::Static { term } => {
                self.collect_certified_replay_term_calls(*term, calls, visited_terms);
            }
            TermTemplate::Call { sort, op, children } => {
                calls.insert((*sort, *op));
                for child in children.iter() {
                    self.collect_certified_template_calls(child, calls, visited_terms);
                }
            }
        }
    }

    fn public_cause(cause: CauseRef) -> Result<ReceiptCauseRef, ReceiptViewError> {
        if cause.is_unattributed() {
            return Err(ReceiptViewError::Invalid(
                "durable event has an unattributed cause".into(),
            ));
        }
        if let Some(rule) = cause.rule_match() {
            return Ok(ReceiptCauseRef::Rule(rule));
        }
        let draft = cause.cause_node().ok_or_else(|| {
            ReceiptViewError::Invalid("durable event has no cause identity".into())
        })?;
        let id = u32::try_from(draft.get())
            .map_err(|_| ReceiptViewError::Invalid("receipt cause identity exceeds u32".into()))?;
        Ok(ReceiptCauseRef::Cause(ReceiptCauseId::new(id)))
    }

    pub fn totals(&self) -> CausalReceiptTotals {
        CausalReceiptTotals {
            facts: self.arena.published_facts,
            matches: self.arena.published_matches,
            causes: self.arena.published_causes,
            applied_equalities: self.arena.published_equalities,
            rekeys: self.arena.rekeys.len() as u64,
            removals: self.arena.removals.len() as u64,
            check_roots: self.arena.check_roots.len() as u64,
        }
    }

    pub fn view_counters(&self) -> CausalReceiptViewCounters {
        self.counters
    }

    pub fn counters(&self) -> ReceiptCounters {
        self.arena.counters
    }

    pub fn fact(&self, id: FactId) -> Result<RawFactRecord<'a>, ReceiptViewError> {
        if id.is_missing() {
            return Err(ReceiptViewError::UnknownFact(id));
        }
        let fact = self
            .arena
            .facts
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownFact(id))?;
        Ok(RawFactRecord {
            id,
            table: fact.table,
            position: fact.position,
            cause: Self::public_cause(fact.cause)?,
            values: &self.arena.durable_fact_values[fact.values.as_range()],
        })
    }

    fn rekey_index(&mut self) -> &RekeyIndex {
        if self.rekey_index.is_none() {
            let mut by_fact = HashMap::<FactId, Vec<usize>>::default();
            let mut by_position = HashMap::default();
            for (index, rekey) in self.arena.rekeys.iter().enumerate() {
                by_fact.entry(rekey.fact).or_default().push(index);
                assert!(
                    by_position.insert(rekey.position, index).is_none(),
                    "two logical rekeys share one history position"
                );
            }
            self.rekey_index = Some(RekeyIndex {
                by_fact: by_fact
                    .into_iter()
                    .map(|(fact, indexes)| (fact, Arc::from(indexes)))
                    .collect(),
                by_position,
            });
        }
        self.rekey_index.as_ref().unwrap()
    }

    pub fn matched(&self, id: RuleMatchId) -> Result<RawMatchRecord<'a>, ReceiptViewError> {
        if id.get() == 0 {
            return Err(ReceiptViewError::UnknownMatch(id));
        }
        let matched = self
            .arena
            .durable_matches
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownMatch(id))?;
        let merge_reads = self
            .arena
            .merge_reads
            .get(&id)
            .map_or(&[][..], SmallVec::as_slice);
        Ok(RawMatchRecord {
            id,
            rule: matched.rule,
            wave: matched.wave,
            position: matched.position,
            as_of_edges: matched.as_of_edges,
            premises: &self.arena.durable_premises[matched.premises.as_range()],
            merge_reads,
        })
    }

    pub fn cause(&self, id: ReceiptCauseId) -> Result<RawReceiptCause<'a>, ReceiptViewError> {
        if id.get() == 0 {
            return Err(ReceiptViewError::UnknownCause(id));
        }
        let cause = self
            .arena
            .durable_cause(CauseDraftId::new(id.get() as u64))
            .ok_or(ReceiptViewError::UnknownCause(id))?;
        Ok(match cause {
            DurableCause::Source(source) => RawReceiptCause::Source(source),
            DurableCause::Rebuild {
                wave,
                prior_fact,
                as_of_edges,
                position,
                equalities,
            } => RawReceiptCause::Rebuild {
                wave: *wave,
                prior_fact: *prior_fact,
                as_of_edges: *as_of_edges,
                position: *position,
                equalities: &self.arena.durable_rebuild_equalities[equalities.as_range()],
            },
            DurableCause::ContainerCanonicalize {
                wave,
                as_of_edges,
                position,
                equalities,
            } => RawReceiptCause::ContainerCanonicalize {
                wave: *wave,
                as_of_edges: *as_of_edges,
                position: *position,
                equalities: &self.arena.durable_rebuild_equalities[equalities.as_range()],
            },
            DurableCause::ContainerRefresh {
                wave,
                prior_fact,
                as_of_edges,
                position,
                equalities,
            } => RawReceiptCause::ContainerRefresh {
                wave: *wave,
                prior_fact: *prior_fact,
                as_of_edges: *as_of_edges,
                position: *position,
                equalities: &self.arena.durable_rebuild_equalities[equalities.as_range()],
            },
            DurableCause::Merge { incoming, prior } => RawReceiptCause::Merge {
                incoming: Self::public_cause(*incoming)?,
                prior: match prior {
                    DurablePrior::Fact(fact) => ReceiptCausePrior::Fact(*fact),
                    DurablePrior::Cause(cause) => {
                        ReceiptCausePrior::Cause(Self::public_cause(*cause)?)
                    }
                },
            },
        })
    }

    pub fn applied_equality(
        &self,
        id: AppliedEqualityId,
    ) -> Result<RawAppliedEquality, ReceiptViewError> {
        if id.get() == 0 {
            return Err(ReceiptViewError::UnknownEquality(id));
        }
        let event = self
            .arena
            .durable_equalities
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownEquality(id))?;
        Ok(RawAppliedEquality {
            id,
            wave: event.proposal.wave,
            position: event.position,
            left: RawEqualityEndpoint {
                sort: event.proposal.left.sort,
                raw: event.proposal.left.raw,
            },
            right: RawEqualityEndpoint {
                sort: event.proposal.right.sort,
                raw: event.proposal.right.raw,
            },
            native_parent: event.native_parent,
            native_child: event.native_child,
            reason: self.arena.equality_reason(event.cause),
        })
    }

    pub fn project_applied_equality(
        &mut self,
        id: AppliedEqualityId,
    ) -> Result<ProjectedAppliedEquality, ReceiptViewError> {
        if id.get() == 0 {
            return Err(ReceiptViewError::UnknownEquality(id));
        }
        let event = self
            .arena
            .durable_equalities
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownEquality(id))?;
        let left = self
            .projector
            .equality_endpoint(event.proposal.left, event.cause, event.position)
            .map_err(ReceiptViewError::Invalid)?;
        let right = self
            .projector
            .equality_endpoint(event.proposal.right, event.cause, event.position)
            .map_err(ReceiptViewError::Invalid)?;
        Ok(ProjectedAppliedEquality {
            id,
            wave: event.proposal.wave,
            position: event.position,
            left,
            right,
            native_parent: event.native_parent,
            native_child: event.native_child,
            reason: self.arena.equality_reason(event.cause),
        })
    }

    pub fn rekey_at(
        &mut self,
        position: HistoryPosition,
    ) -> Result<RawRekeyRecord<'a>, ReceiptViewError> {
        self.counters.rekey_lookups += 1;
        let index = self
            .rekey_index()
            .by_position
            .get(&position)
            .copied()
            .ok_or(ReceiptViewError::UnknownRekey(position))?;
        self.counters.rekey_records_scanned += 1;
        let record = &self.arena.rekeys[index];
        Ok(RawRekeyRecord {
            fact: record.fact,
            table: record.table,
            wave: record.wave,
            position: record.position,
            as_of_edges: record.equalities.as_of_edges,
            equality_position: record.equalities.position,
            equalities: &record.equalities.pairs,
            outcome: record.outcome,
        })
    }

    pub fn removal(&self, index: usize) -> Result<&'a RemovalRecord, ReceiptViewError> {
        self.arena
            .removals
            .get(index)
            .ok_or(ReceiptViewError::UnknownRemoval(index))
    }

    pub fn check_root(&self, check: u32) -> Result<&'a CheckRoot, ReceiptViewError> {
        self.arena
            .check_roots
            .get(&check)
            .ok_or(ReceiptViewError::UnknownCheck(check))
    }

    pub fn check_roots(&self) -> Vec<&'a CheckRoot> {
        let mut roots = self.arena.check_roots.values().collect::<Vec<_>>();
        roots.sort_unstable_by_key(|root| root.check);
        roots
    }

    pub fn table_schema(&self, table: TableId) -> Result<ReplayTableSchema, ReceiptViewError> {
        let columns = self
            .replay_terms
            .table_layout(table)
            .ok_or(ReceiptViewError::UnknownTable(table))?;
        let kind = self
            .replay_terms
            .table_kinds
            .get(&table)
            .map(|kind| *kind)
            .ok_or(ReceiptViewError::UnknownTable(table))?;
        let key_columns = self
            .replay_terms
            .table_key_columns
            .get(&table)
            .map(|columns| *columns as usize)
            .ok_or(ReceiptViewError::UnknownTable(table))?;
        let constructor = self
            .replay_terms
            .table_constructors
            .get(&table)
            .map(|constructor| constructor.clone());
        Ok(ReplayTableSchema {
            table,
            kind,
            key_columns,
            columns,
            constructor,
        })
    }

    pub fn rule_binding_layout(
        &self,
        rule: u32,
    ) -> Result<Box<[ReceiptBindingSource]>, ReceiptViewError> {
        let bindings = self.binding_recipes.get(&rule).ok_or_else(|| {
            ReceiptViewError::Invalid(format!("rule {rule} has no binding recipe"))
        })?;
        let current_roots = self
            .term_recipes
            .rules
            .get(&rule)
            .map(|recipe| recipe.current_roots.as_ref())
            .unwrap_or(&[]);
        bindings
            .iter()
            .map(|binding| {
                Ok(match binding {
                    ReplayBindingSource::Premise {
                        representative,
                        occurrences,
                    } => ReceiptBindingSource::Premise {
                        representative: ReceiptPremiseOccurrence {
                            premise: representative.premise,
                            column: representative.column,
                        },
                        occurrences: occurrences
                            .iter()
                            .map(|occurrence| ReceiptPremiseOccurrence {
                                premise: occurrence.premise,
                                column: occurrence.column,
                            })
                            .collect(),
                    },
                    ReplayBindingSource::Current { sort, residual, .. } => {
                        ReceiptBindingSource::Current {
                            sort: *sort,
                            residual: *residual,
                            replay_safe: current_roots
                                .get(*residual as usize)
                                .is_some_and(Option::is_some),
                        }
                    }
                    ReplayBindingSource::Constant { term } => {
                        ReceiptBindingSource::Constant { term: *term }
                    }
                })
            })
            .collect::<Result<Vec<_>, ReceiptViewError>>()
            .map(Vec::into_boxed_slice)
    }

    pub fn rule_equality_layout(
        &self,
        rule: u32,
    ) -> Result<Box<[(ReceiptEqualitySource, ReceiptEqualitySource)]>, ReceiptViewError> {
        let equalities = self.equality_recipes.get(&rule).ok_or_else(|| {
            ReceiptViewError::Invalid(format!("rule {rule} has no equality-obligation recipe"))
        })?;
        Ok(equalities
            .iter()
            .map(|&(left, right)| {
                let public = |source| match source {
                    ReplayEqualitySource::Premise(occurrence) => {
                        ReceiptEqualitySource::Premise(ReceiptPremiseOccurrence {
                            premise: occurrence.premise,
                            column: occurrence.column,
                        })
                    }
                    ReplayEqualitySource::Constant(endpoint) => {
                        ReceiptEqualitySource::Constant(endpoint)
                    }
                };
                (public(left), public(right))
            })
            .collect::<Vec<_>>()
            .into_boxed_slice())
    }

    pub fn fact_terms(&mut self, id: FactId) -> Result<Box<[ReplayTermId]>, ReceiptViewError> {
        let fact = self.fact(id)?;
        let layout = self
            .replay_terms
            .table_layout(fact.table)
            .ok_or(ReceiptViewError::UnknownTable(fact.table))?;
        layout
            .iter()
            .enumerate()
            .map(|(column, sort)| {
                sort.map_or(Ok(ReplayTermId::MISSING), |_| {
                    self.projector
                        .fact_term(id, column)
                        .map_err(ReceiptViewError::Invalid)
                })
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Vec::into_boxed_slice)
    }

    pub fn match_terms(
        &mut self,
        id: RuleMatchId,
    ) -> Result<Box<[ReplayTermId]>, ReceiptViewError> {
        let matched = self.matched(id)?;
        let binding_count = self
            .binding_recipes
            .get(&matched.rule)
            .ok_or_else(|| {
                ReceiptViewError::Invalid(format!("rule {} has no binding recipe", matched.rule))
            })?
            .len();
        (0..binding_count)
            .map(|binding| {
                self.projector
                    .match_term(id, binding)
                    .map_err(ReceiptViewError::Invalid)
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Vec::into_boxed_slice)
    }

    /// Prove that one complete grounded binding can be named by `let-check`
    /// at the match's historical position. Unlike equality explanation this
    /// asks only for structural availability: pure calls and ordered
    /// containers are recomputed from their children, while every table
    /// constructor must have one exact live producer row.
    pub fn explain_match_term_availability(
        &mut self,
        id: RuleMatchId,
        binding: usize,
    ) -> Result<RawTermAvailability, ReceiptViewError> {
        let (rule, position, as_of_edges, premises) = {
            let matched = self.matched(id)?;
            (
                matched.rule,
                matched.position,
                matched.as_of_edges,
                matched.premises.to_vec(),
            )
        };
        let binding_source = self
            .binding_recipes
            .get(&rule)
            .and_then(|sources| sources.get(binding))
            .cloned()
            .ok_or_else(|| {
                ReceiptViewError::Invalid(format!("rule {rule} has no binding source {binding}"))
            })?;
        let anchor = match &binding_source {
            ReplayBindingSource::Premise { representative, .. } => {
                let fact = *premises.get(representative.premise).ok_or_else(|| {
                    ReceiptViewError::Invalid(format!(
                        "match {id:?} has no premise {}",
                        representative.premise
                    ))
                })?;
                Some(self.fact_cell_at(
                    FactCellRef {
                        fact,
                        column: crate::ColumnId::from_usize(representative.column),
                    },
                    position,
                )?)
            }
            ReplayBindingSource::Current { .. } | ReplayBindingSource::Constant { .. } => None,
        };
        let term = self
            .projector
            .match_term(id, binding)
            .map_err(ReceiptViewError::Invalid)?;
        let availability = (|| {
            if let Some(anchor) = anchor {
                let endpoint = EqualityEndpoint {
                    sort: anchor.endpoint.sort,
                    term,
                    raw: anchor.endpoint.raw,
                };
                self.explain_anchored_term_availability_at(
                    endpoint,
                    anchor,
                    as_of_edges,
                    position,
                )
            } else {
                let mut aliases = Vec::new();
                let support = self.explain_structural_term_availability_at(
                    term,
                    position,
                    0,
                    &mut aliases,
                    None,
                    None,
                )?;
                Ok(RawTermAvailability {
                    support,
                    aliases: aliases.into_boxed_slice(),
                })
            }
        })()
            .map_err(|error| {
                ReceiptViewError::Invalid(format!(
                    "match {id:?} rule {rule} binding {binding} ({binding_source:?}) availability failed: {error}"
                ))
            })?;
        Ok(availability)
    }

    pub fn explain_fact_endpoint_availability_at(
        &mut self,
        occurrence: FactCellRef,
        endpoint: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawTermAvailability, ReceiptViewError> {
        let anchor = self.fact_cell_at(occurrence, position)?;
        self.explain_anchored_term_availability_at(endpoint, anchor, as_of, position)
    }

    fn explain_anchored_term_availability_at(
        &mut self,
        endpoint: EqualityEndpoint,
        anchor: HistoricalFactCell,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawTermAvailability, ReceiptViewError> {
        self.validate_equality_cutoff(as_of, position)?;
        if endpoint.sort != anchor.endpoint.sort {
            return Err(ReceiptViewError::Invalid(
                "anchored structural term has the wrong logical sort".into(),
            ));
        }
        let mut aliases = Vec::new();
        let structural = self.explain_structural_term_availability_at(
            endpoint.term,
            position,
            0,
            &mut aliases,
            Some(RawEqualityEndpoint {
                sort: endpoint.sort,
                raw: endpoint.raw,
            }),
            Some(&anchor),
        )?;
        let bridge = if endpoint.raw == anchor.endpoint.raw {
            RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            }
        } else {
            self.explain_raw_equality_support_at(
                RawEqualityEndpoint {
                    sort: endpoint.sort,
                    raw: endpoint.raw,
                },
                RawEqualityEndpoint {
                    sort: anchor.endpoint.sort,
                    raw: anchor.endpoint.raw,
                },
                as_of,
                position,
            )?
        };
        let anchor = RawEqualitySupport {
            applied: Box::new([]),
            facts: Box::new([anchor.occurrence.fact]),
            causes: Box::new([]),
            rekeys: anchor.rekeys,
        };
        Ok(RawTermAvailability {
            support: combine_raw_equality_support([structural, bridge, anchor]),
            aliases: aliases.into_boxed_slice(),
        })
    }

    pub fn replay_term(&self, term: ReplayTermId) -> Result<ReplayTerm, ReceiptViewError> {
        self.replay_terms
            .node(term)
            .ok_or_else(|| ReceiptViewError::Invalid(format!("unknown replay term {term:?}")))
    }

    fn live_fact_at(
        &self,
        fact: FactId,
        position: HistoryPosition,
    ) -> Result<RawFactRecord<'a>, ReceiptViewError> {
        if position > self.history_boundary {
            return Err(ReceiptViewError::Invalid(
                "fact query exceeds the captured receipt history".into(),
            ));
        }
        let record = self.fact(fact)?;
        if record.position > position {
            return Err(ReceiptViewError::Invalid(format!(
                "fact {fact:?} was created after {position:?}"
            )));
        }
        if let Some(removal) = self
            .arena
            .removals
            .iter()
            .find(|removal| removal.removed_fact == fact && removal.position <= position)
        {
            return Err(ReceiptViewError::FactNoLongerLive {
                fact,
                position,
                ended_at: removal.position,
                successor: None,
            });
        }
        Ok(record)
    }

    pub fn fact_cell_at(
        &mut self,
        occurrence: FactCellRef,
        position: HistoryPosition,
    ) -> Result<HistoricalFactCell, ReceiptViewError> {
        let fact = self.live_fact_at(occurrence.fact, position)?;
        let column = occurrence.column.index();
        let sort = self
            .replay_terms
            .table_layout(fact.table)
            .ok_or(ReceiptViewError::UnknownTable(fact.table))?
            .get(column)
            .copied()
            .flatten()
            .ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "fact {:?} column {column} has no logical replay sort",
                    occurrence.fact
                ))
            })?;
        let term = self
            .projector
            .fact_term(occurrence.fact, column)
            .map_err(ReceiptViewError::Invalid)?;
        let creation_raw = *fact.values.get(column).ok_or_else(|| {
            ReceiptViewError::Invalid(format!("fact {:?} has no column {column}", occurrence.fact))
        })?;
        let mut raw = creation_raw;
        let mut rekeys = Vec::new();
        let fact_rekeys = self
            .rekey_index()
            .by_fact
            .get(&occurrence.fact)
            .cloned()
            .unwrap_or_else(|| Arc::from([]));
        for index in fact_rekeys.iter().copied() {
            let rekey = &self.arena.rekeys[index];
            if rekey.position > position {
                break;
            }
            for pair in rekey
                .equalities
                .pairs
                .iter()
                .filter(|pair| pair.column == occurrence.column)
            {
                if pair.left.raw != raw || pair.left.sort != sort || pair.right.sort != sort {
                    return Err(ReceiptViewError::Invalid(format!(
                        "rekey {:?} does not continue fact-cell occurrence {:?}: expected {:?}/{:?}, observed {:?}, outcome {:?}",
                        rekey.position, occurrence, sort, raw, pair, rekey.outcome
                    )));
                }
                raw = pair.right.raw;
                rekeys.push(rekey.position);
            }
            if rekey.outcome != RekeyOutcome::Moved {
                let successor = match rekey.outcome {
                    RekeyOutcome::Moved => unreachable!(),
                    RekeyOutcome::Absorbed(fact) | RekeyOutcome::Replaced(fact) => fact,
                };
                return Err(ReceiptViewError::FactNoLongerLive {
                    fact: occurrence.fact,
                    position,
                    ended_at: rekey.position,
                    successor: Some(successor),
                });
            }
        }
        Ok(HistoricalFactCell {
            occurrence,
            created: EqualityEndpoint {
                sort,
                term,
                raw: creation_raw,
            },
            endpoint: EqualityEndpoint { sort, term, raw },
            rekeys: rekeys.into_boxed_slice(),
        })
    }

    pub fn fact_key_at(
        &mut self,
        fact: FactId,
        position: HistoryPosition,
    ) -> Result<Box<[Value]>, ReceiptViewError> {
        let record = self.live_fact_at(fact, position)?;
        let schema = self.table_schema(record.table)?;
        (0..schema.key_columns)
            .map(|column| {
                if schema.columns[column].is_some() {
                    self.fact_cell_at(
                        FactCellRef {
                            fact,
                            column: crate::ColumnId::new(column.try_into().map_err(|_| {
                                ReceiptViewError::Invalid("table key column exceeds u32".into())
                            })?),
                        },
                        position,
                    )
                    .map(|cell| cell.endpoint.raw)
                } else {
                    record.values.get(column).copied().ok_or_else(|| {
                        ReceiptViewError::Invalid(format!(
                            "fact {fact:?} has no key column {column}"
                        ))
                    })
                }
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Vec::into_boxed_slice)
    }

    fn validate_equality_cutoff(
        &self,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<usize, ReceiptViewError> {
        let cutoff: usize = as_of.get().try_into().map_err(|_| {
            ReceiptViewError::Invalid("equality cutoff exceeds addressable storage".into())
        })?;
        if cutoff > self.arena.durable_equalities.len() {
            return Err(ReceiptViewError::Invalid(
                "equality cutoff exceeds the raw applied-event history".into(),
            ));
        }
        if position > self.history_boundary {
            return Err(ReceiptViewError::Invalid(
                "equality query exceeds the captured receipt history".into(),
            ));
        }
        let previous_visible = cutoff
            .checked_sub(1)
            .map(|index| {
                self.arena.durable_equalities[index]
                    .as_ref()
                    .ok_or_else(|| {
                        ReceiptViewError::Invalid(
                            "raw applied-equality history has an ID hole".into(),
                        )
                    })
                    .map(|event| event.position <= position)
            })
            .transpose()?
            .unwrap_or(true);
        let next_hidden = self
            .arena
            .durable_equalities
            .get(cutoff)
            .map(|event| {
                event
                    .as_ref()
                    .ok_or_else(|| {
                        ReceiptViewError::Invalid(
                            "raw applied-equality history has an ID hole".into(),
                        )
                    })
                    .map(|event| event.position > position)
            })
            .transpose()?
            .unwrap_or(true);
        if !previous_visible || !next_hidden {
            return Err(ReceiptViewError::Invalid(
                "equality cutoff disagrees with the global history position".into(),
            ));
        }
        Ok(cutoff)
    }
}

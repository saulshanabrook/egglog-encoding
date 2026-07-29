//! Borrowed historical views over one publication-complete trace.

use super::*;

#[path = "explain.rs"]
mod explain;

/// Lazy historical projector shared by borrowed views and runtime container
/// anchoring. Native capture stores raw creation rows and compact static origin
/// sites; consumers expand only the requested references into the replay-term
/// DAG.
#[derive(Clone)]
enum TemplateOwner {
    Durable(FiringId),
    Fact(FactId),
    History {
        position: HistoryPosition,
        inclusive: bool,
    },
}

pub(super) struct TermProjector<'a> {
    arena: &'a TraceArena,
    binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
    term_recipes: &'a StaticTermRecipeStore,
    replay_terms: &'a TermInterner,
    next_term: &'a AtomicU32,
    fact_memo: HashMap<(FactId, usize), ReplayTermId>,
    firing_memo: HashMap<(FiringId, usize), ReplayTermId>,
    visiting_facts: HashSet<(FactId, usize)>,
    visiting_firings: HashSet<(FiringId, usize)>,
}

impl<'a> TermProjector<'a> {
    pub(super) fn new(
        arena: &'a TraceArena,
        binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
        term_recipes: &'a StaticTermRecipeStore,
        replay_terms: &'a TermInterner,
        next_term: &'a AtomicU32,
    ) -> Self {
        Self {
            arena,
            binding_recipes,
            term_recipes,
            replay_terms,
            next_term,
            fact_memo: HashMap::default(),
            firing_memo: HashMap::default(),
            visiting_facts: HashSet::default(),
            visiting_firings: HashSet::default(),
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
                .ok_or_else(|| format!("unknown trace fact {fact_id:?}"))?;
            let owner = self
                .arena
                .originating_rule(fact.cause)
                .map(TemplateOwner::Durable)
                .unwrap_or(TemplateOwner::Fact(fact_id));
            let merge_cell = match fact.origin {
                Some(FactOrigin::Merge { cells, .. }) => self.arena.durable_merge_cell_origins
                    [cells.as_range()]
                .get(column)
                .copied(),
                _ => None,
            };
            let (table, origin) = (fact.table, fact.origin);
            match origin {
                Some(FactOrigin::Site(site)) => self.site_term(site, table, column, Some(&owner)),
                Some(FactOrigin::Fact(source)) => self.fact_term(source, column),
                Some(FactOrigin::Merge {
                    incoming, prior, ..
                }) => {
                    let cell = merge_cell.ok_or_else(|| {
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

    fn firing_term(&mut self, firing_id: FiringId, binding: usize) -> Result<ReplayTermId, String> {
        if let Some(term) = self.firing_memo.get(&(firing_id, binding)).copied() {
            return Ok(term);
        }
        if !self.visiting_firings.insert((firing_id, binding)) {
            return Err(format!(
                "cyclic firing term at {firing_id:?} binding {binding}"
            ));
        }
        let result = (|| {
            let arena = self.arena;
            let record = arena
                .durable_firings
                .get((firing_id.get().checked_sub(1).ok_or("missing FiringId")?) as usize)
                .and_then(Option::as_ref)
                .ok_or_else(|| format!("unknown firing {firing_id:?}"))?;
            let rule = record.rule;
            let premises = &arena.durable_premises[record.premises.as_range()];
            self.binding_term(rule, premises, binding, &TemplateOwner::Durable(firing_id))
        })();
        self.visiting_firings.remove(&(firing_id, binding));
        let term = result?;
        self.firing_memo.insert((firing_id, binding), term);
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
                TemplateOwner::Durable(firing_id) => {
                    self.firing_term(*firing_id, *binding as usize)
                }
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
                    TemplateOwner::Durable(firing_id) => {
                        let record = self
                            .arena
                            .durable_firings
                            .get(
                                (firing_id.get().checked_sub(1).ok_or("missing FiringId")?)
                                    as usize,
                            )
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown firing {firing_id:?}"))?;
                        *self
                            .arena
                            .durable_premises
                            .get(record.premises.as_range())
                            .and_then(|premises| premises.get(*premise as usize))
                            .ok_or_else(|| {
                                format!("firing {firing_id:?} has no premise {premise}")
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
                    TemplateOwner::Durable(firing_id) => (
                        self.arena
                            .durable_firings
                            .get(
                                (firing_id.get().checked_sub(1).ok_or("missing FiringId")?)
                                    as usize,
                            )
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown firing {firing_id:?}"))?
                            .history_cutoff,
                        true,
                    ),
                    TemplateOwner::Fact(fact) => (
                        self.arena
                            .facts
                            .get((fact.get().checked_sub(1).ok_or("missing FactId")?) as usize)
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown trace fact {fact:?}"))?
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
        cause: PackedCauseRef,
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

/// Borrowed, non-escaping view of quiescent, publication-complete history.
///
/// Accessors project structural terms only for explicitly selected facts,
/// firings, or equality events. Historical explanation indexes and occurrence
/// caches are likewise constructed only when an `explain_*` query needs them.
/// A view can be obtained only through [`Trace::with_view`], whose closure
/// prevents references into the arena from escaping. The view check does not
/// freeze independent term/catalog writers; callers needing a stable catalog
/// must quiesce them before entry.
pub struct TraceView<'a> {
    pub(super) arena: &'a TraceArena,
    pub(super) binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
    pub(super) equality_recipes:
        &'a HashMap<u32, Arc<[(FiringEqualitySource, FiringEqualitySource)]>>,
    pub(super) term_recipes: &'a StaticTermRecipeStore,
    pub(super) replay_terms: &'a TermInterner,
    pub(super) projector: TermProjector<'a>,
    pub(super) history_boundary: HistoryPosition,
    pub(super) equality_index: Option<ExplanationForest>,
    pub(super) rekey_index: Option<VersionChain>,
    pub(super) constructor_occurrence_index: Option<ConstructorOccurrenceIndex>,
    pub(super) occurrence_support_cache:
        HashMap<StructuralOccurrenceQuery, Option<RawEqualitySupport>>,
    pub(super) exact_occurrence_support_cache:
        HashMap<StructuralOccurrenceQuery, Option<RawEqualitySupport>>,
}

pub(super) struct ExplanationForest {
    parents: HashMap<(ReplaySortId, Value), (Value, AppliedEqualityId)>,
}

pub(super) struct VersionChain {
    by_fact: HashMap<FactId, Arc<[usize]>>,
    by_position: HashMap<HistoryPosition, usize>,
}

pub(super) struct ConstructorOccurrenceIndex {
    facts: HashMap<(ReplaySortId, ReplayOpId), Arc<[FactId]>>,
    registered: HashSet<(ReplaySortId, ReplayOpId)>,
    equality_sorts: HashSet<ReplaySortId>,
    /// Non-table calls that were emitted by a frontend-certified static term
    /// recipe. Only these calls may be recomputed by `let-check` without a
    /// constructor FactId. Building this set is deliberately cold: capture
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
    retain_exact_producer: bool,
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

impl<'a> TraceView<'a> {
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

    fn public_cause(cause: PackedCauseRef) -> Result<CauseRef, TraceViewError> {
        if cause.is_unattributed() {
            return Err(TraceViewError::Invalid(
                "durable event has an unattributed cause".into(),
            ));
        }
        if let Some(rule) = cause.firing() {
            return Ok(CauseRef::Rule(rule));
        }
        let draft = cause
            .cause_node()
            .ok_or_else(|| TraceViewError::Invalid("durable event has no cause identity".into()))?;
        let id = u32::try_from(draft.get())
            .map_err(|_| TraceViewError::Invalid("capture cause identity exceeds u32".into()))?;
        Ok(CauseRef::Cause(CauseId::new(id)))
    }

    /// Return point-in-time cardinalities of the checked trace view.
    ///
    /// The fields count the dense record families traversed by backward
    /// selection. Firings, rekeys, and criteria are reached from their owning
    /// records or dedicated indexes instead of duplicated here.
    pub fn totals(&self) -> TraceTotals {
        TraceTotals {
            facts: self.arena.published_facts,
            applied_equalities: self.arena.published_equalities,
            removals: self.arena.removals.len() as u64,
        }
    }

    /// Borrow one immutable fact-creation record by its stable id.
    ///
    /// The returned raw values are the row at creation time. Later rekeys do
    /// not mutate them; use [`TraceView::fact_cell_at`] for a historical
    /// post-rekey cell value.
    pub fn fact(&self, id: FactId) -> Result<RawFactRecord<'a>, TraceViewError> {
        if id.is_missing() {
            return Err(TraceViewError::UnknownFact(id));
        }
        let fact = self
            .arena
            .facts
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(TraceViewError::UnknownFact(id))?;
        Ok(RawFactRecord {
            table: fact.table,
            position: fact.position,
            cause: Self::public_cause(fact.cause)?,
            values: &self.arena.durable_fact_values[fact.values.as_range()],
        })
    }

    fn rekey_index(&mut self) -> &VersionChain {
        if self.rekey_index.is_none() {
            let mut by_fact = HashMap::<FactId, Vec<usize>>::default();
            let mut by_position = HashMap::default();
            by_position.reserve(self.arena.rekeys.len());
            for (index, rekey) in self.arena.rekeys.iter().enumerate() {
                by_fact.entry(rekey.fact).or_default().push(index);
                assert!(
                    by_position.insert(rekey.position, index).is_none(),
                    "two logical rekeys share one history position"
                );
            }
            self.rekey_index = Some(VersionChain {
                by_fact: by_fact
                    .into_iter()
                    .map(|(fact, indexes)| (fact, Arc::from(indexes)))
                    .collect(),
                by_position,
            });
        }
        self.rekey_index.as_ref().unwrap()
    }

    /// Borrow one observed rule firing and its exact grounded dependencies.
    ///
    /// `premises` are the matched fact occurrences in the rule's premise
    /// order. `merge_reads` are additional prior rows consulted by effective
    /// merge callbacks. The sampled history cutoff bounds every explanation of
    /// what the firing observed, including its derived equality prefix.
    pub fn firing(&self, id: FiringId) -> Result<Firing<'a>, TraceViewError> {
        if id.get() == 0 {
            return Err(TraceViewError::UnknownFiring(id));
        }
        let firing = self
            .arena
            .durable_firings
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(TraceViewError::UnknownFiring(id))?;
        let merge_reads = self
            .arena
            .merge_reads
            .get(&id)
            .map_or(&[][..], SmallVec::as_slice);
        Ok(Firing {
            rule: firing.rule,
            wave: firing.wave,
            history_cutoff: firing.history_cutoff,
            premises: &self.arena.durable_premises[firing.premises.as_range()],
            merge_reads,
        })
    }

    /// Borrow prior rows consulted by merge callbacks in one source action bundle.
    ///
    /// Replaying any selected effect from the bundle re-executes all of its
    /// visible sibling effects, so their merge predecessors are dependencies
    /// of the source carrier as a whole.
    pub fn source_merge_reads(&self, source: &SourceRef) -> &[FactId] {
        self.arena
            .source_merge_reads
            .get(source)
            .map_or(&[], SmallVec::as_slice)
    }

    /// Borrow one shared non-rule cause node without recursively expanding it.
    ///
    /// Source, rebuild, container, and merge causes expose only their immediate
    /// dependencies. Consumers can follow returned [`CauseRef`] and [`FactId`]
    /// handles lazily, so inspecting one node does not walk the causal graph.
    pub fn cause(&self, id: CauseId) -> Result<RawCause<'a>, TraceViewError> {
        if id.get() == 0 {
            return Err(TraceViewError::UnknownCause(id));
        }
        let cause = self
            .arena
            .durable_cause(CauseDraftId::new(id.get() as u64))
            .ok_or(TraceViewError::UnknownCause(id))?;
        Ok(match cause {
            DurableCause::Source(source) => RawCause::Source(source),
            DurableCause::Rebuild {
                prior_fact,
                position,
                equalities,
            } => RawCause::Rebuild {
                prior_fact: *prior_fact,
                position: *position,
                equalities: &self.arena.durable_cell_equalities[equalities.as_range()],
            },
            DurableCause::ContainerCanonicalize {
                position,
                equalities,
            } => RawCause::ContainerCanonicalize {
                position: *position,
                equalities: &self.arena.durable_cell_equalities[equalities.as_range()],
            },
            DurableCause::ContainerRefresh {
                prior_fact,
                position,
                equalities,
            } => RawCause::ContainerRefresh {
                prior_fact: *prior_fact,
                position: *position,
                equalities: &self.arena.durable_cell_equalities[equalities.as_range()],
            },
            DurableCause::Merge {
                incoming,
                prior_fact,
            } => RawCause::Merge {
                incoming: Self::public_cause(*incoming)?,
                prior_fact: *prior_fact,
            },
        })
    }

    /// Return one effective equality event without projecting structural terms.
    ///
    /// The raw endpoints are the typed proposal values. `native_child` and
    /// `native_parent` are the forest edge that actually changed the native
    /// union-find, which can differ from the proposal values' representatives.
    /// Use [`TraceView::project_applied_equality`] when replay syntax is needed.
    pub fn applied_equality(
        &self,
        id: AppliedEqualityId,
    ) -> Result<RawAppliedEquality, TraceViewError> {
        if id.get() == 0 {
            return Err(TraceViewError::UnknownEquality(id));
        }
        let event = self
            .arena
            .durable_equalities
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(TraceViewError::UnknownEquality(id))?;
        Ok(RawAppliedEquality {
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

    /// Return the lazily reconstructed structural proposal for an applied equality.
    ///
    /// Projection follows the event's retained cause/origin metadata and
    /// memoizes only the selected fact and firing terms. The result preserves
    /// the exact reason; the native edge and event position remain available
    /// from [`TraceView::applied_equality`].
    pub fn project_applied_equality(
        &mut self,
        id: AppliedEqualityId,
    ) -> Result<ProjectedEqualityProposal, TraceViewError> {
        if id.get() == 0 {
            return Err(TraceViewError::UnknownEquality(id));
        }
        let event = self
            .arena
            .durable_equalities
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(TraceViewError::UnknownEquality(id))?;
        let left = self
            .projector
            .equality_endpoint(event.proposal.left, event.cause, event.position)
            .map_err(TraceViewError::Invalid)?;
        let right = self
            .projector
            .equality_endpoint(event.proposal.right, event.cause, event.position)
            .map_err(TraceViewError::Invalid)?;
        Ok(ProjectedEqualityProposal {
            left,
            right,
            reason: self.arena.equality_reason(event.cause),
        })
    }

    /// Borrow the logical rekey published at an exact global history position.
    ///
    /// The record includes its earlier equality landmark, changed typed cells,
    /// and whether the same fact moved or its occurrence ended in a collision.
    /// Positions without a retained rekey return [`TraceViewError::UnknownRekey`].
    pub fn rekey_at(
        &mut self,
        position: HistoryPosition,
    ) -> Result<RawRekeyRecord<'a>, TraceViewError> {
        let index = self
            .rekey_index()
            .by_position
            .get(&position)
            .copied()
            .ok_or(TraceViewError::UnknownRekey(position))?;
        let record = &self.arena.rekeys[index];
        Ok(RawRekeyRecord {
            fact: record.fact,
            equality_position: record.equalities.position,
            equalities: &record.equalities.pairs,
            outcome: record.outcome,
        })
    }

    /// Borrow a retained keyed-row tombstone by zero-based storage index.
    ///
    /// This index is not a [`HistoryPosition`]. Presence-relation removals have
    /// no replay-observable merge-bearing cell and therefore no tombstone.
    pub fn removal(&self, index: usize) -> Result<&'a Tombstone, TraceViewError> {
        self.arena
            .removals
            .get(index)
            .ok_or(TraceViewError::UnknownRemoval(index))
    }

    /// Borrow the first successful retained criterion for one check id.
    pub fn check_root(&self, check: u32) -> Result<&'a Criterion, TraceViewError> {
        self.arena
            .check_roots
            .get(&check)
            .ok_or(TraceViewError::UnknownCheck(check))
    }

    /// Return all retained first-success criteria in ascending check-id order.
    ///
    /// The vector owns only the sorted references; each [`Criterion`] remains
    /// borrowed from the trace arena.
    pub fn check_roots(&self) -> Vec<&'a Criterion> {
        let mut roots = self.arena.check_roots.values().collect::<Vec<_>>();
        roots.sort_unstable_by_key(|root| root.check);
        roots
    }

    /// Return the registered replay schema for one physical table.
    ///
    /// The schema combines keyed-row semantics, key arity, logical column
    /// sorts, and optional structural constructor metadata. Missing any
    /// required catalog component is reported as an unknown table.
    pub fn table_schema(&self, table: TableId) -> Result<ReplayTableSchema, TraceViewError> {
        let columns = self
            .replay_terms
            .table_layout(table)
            .ok_or(TraceViewError::UnknownTable(table))?;
        let kind = self
            .replay_terms
            .table_kinds
            .get(&table)
            .map(|kind| *kind)
            .ok_or(TraceViewError::UnknownTable(table))?;
        let key_columns = self
            .replay_terms
            .table_key_columns
            .get(&table)
            .map(|columns| *columns as usize)
            .ok_or(TraceViewError::UnknownTable(table))?;
        Ok(ReplayTableSchema {
            kind,
            key_columns,
            columns,
        })
    }

    /// Return the static premise/constant endpoint pairs checked by one rule.
    ///
    /// The shared slice is source metadata, not a record of which equalities a
    /// particular firing required. Historical support is computed lazily at
    /// that firing's history cutoff.
    pub fn rule_equality_layout(
        &self,
        rule: u32,
    ) -> Result<Arc<[(FiringEqualitySource, FiringEqualitySource)]>, TraceViewError> {
        let equalities = self.equality_recipes.get(&rule).ok_or_else(|| {
            TraceViewError::Invalid(format!("rule {rule} has no equality-obligation recipe"))
        })?;
        Ok(Arc::clone(equalities))
    }

    /// Project the creation-time structural term of every column in one fact.
    ///
    /// The result follows physical column order. Engine-only columns contain
    /// [`ReplayTermId::MISSING`]; typed columns are recovered lazily from the
    /// fact's static or causal origin and memoized for this view.
    #[cfg(test)]
    pub(crate) fn fact_terms(&mut self, id: FactId) -> Result<Box<[ReplayTermId]>, TraceViewError> {
        let fact = self.fact(id)?;
        let layout = self
            .replay_terms
            .table_layout(fact.table)
            .ok_or(TraceViewError::UnknownTable(fact.table))?;
        layout
            .iter()
            .enumerate()
            .map(|(column, sort)| {
                sort.map_or(Ok(ReplayTermId::MISSING), |_| {
                    self.projector
                        .fact_term(id, column)
                        .map_err(TraceViewError::Invalid)
                })
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Vec::into_boxed_slice)
    }

    /// Project all source-order structural bindings for one firing.
    ///
    /// Terms are reconstructed from the rule's static binding recipe and this
    /// firing's exact premises or residual values, then memoized for this view.
    /// Unsupported reached `Current` recipes fail closed.
    pub fn firing_terms(&mut self, id: FiringId) -> Result<Box<[ReplayTermId]>, TraceViewError> {
        let firing = self.firing(id)?;
        let binding_count = self
            .binding_recipes
            .get(&firing.rule)
            .ok_or_else(|| {
                TraceViewError::Invalid(format!("rule {} has no binding recipe", firing.rule))
            })?
            .len();
        (0..binding_count)
            .map(|binding| {
                self.projector
                    .firing_term(id, binding)
                    .map_err(TraceViewError::Invalid)
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Vec::into_boxed_slice)
    }

    /// Establish that one complete grounded binding can be named by `let-check`
    /// at the match's sampled history cutoff. Unlike equality explanation this
    /// asks only for structural availability: pure calls and ordered
    /// containers are recomputed from their children, while every table
    /// constructor must have one exact live producer row.
    pub fn explain_firing_term_availability(
        &mut self,
        id: FiringId,
        binding: usize,
    ) -> Result<RawTermAvailability, TraceViewError> {
        let (rule, history_cutoff, premises) = {
            let firing = self.firing(id)?;
            (firing.rule, firing.history_cutoff, firing.premises.to_vec())
        };
        let binding_source = self
            .binding_recipes
            .get(&rule)
            .and_then(|sources| sources.get(binding))
            .cloned()
            .ok_or_else(|| {
                TraceViewError::Invalid(format!("rule {rule} has no binding source {binding}"))
            })?;
        let anchor = match &binding_source {
            ReplayBindingSource::Premise { representative, .. } => {
                let fact = *premises.get(representative.premise).ok_or_else(|| {
                    TraceViewError::Invalid(format!(
                        "match {id:?} has no premise {}",
                        representative.premise
                    ))
                })?;
                Some(self.fact_cell_at(
                    FactCellRef {
                        fact,
                        column: crate::ColumnId::from_usize(representative.column),
                    },
                    history_cutoff,
                )?)
            }
            ReplayBindingSource::Current { .. } | ReplayBindingSource::Constant { .. } => None,
        };
        let term = self
            .projector
            .firing_term(id, binding)
            .map_err(TraceViewError::Invalid)?;
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
                    history_cutoff,
                )
            } else {
                let mut aliases = Vec::new();
                let support = self.explain_structural_term_availability_at(
                    term,
                    history_cutoff,
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
                TraceViewError::Invalid(format!(
                    "match {id:?} rule {rule} binding {binding} ({binding_source:?}) availability failed: {error}"
                ))
            })?;
        Ok(availability)
    }

    /// Explain when one structural endpoint can be named through an exact fact
    /// cell at a historical landmark.
    ///
    /// The fact cell supplies the occurrence anchor. The result combines
    /// structural producer support, any raw-equality bridge to the anchor, the
    /// cell's rekey chain, and child-first [`ReplayAliasPlan`] bounds needed for
    /// replay scheduling.
    pub fn explain_fact_endpoint_availability_at(
        &mut self,
        occurrence: FactCellRef,
        endpoint: EqualityEndpoint,
        position: HistoryPosition,
    ) -> Result<RawTermAvailability, TraceViewError> {
        let anchor = self.fact_cell_at(occurrence, position)?;
        self.explain_anchored_term_availability_at(endpoint, anchor, position)
    }

    fn explain_anchored_term_availability_at(
        &mut self,
        endpoint: EqualityEndpoint,
        anchor: HistoricalFactCell,
        position: HistoryPosition,
    ) -> Result<RawTermAvailability, TraceViewError> {
        let equality_prefix = self.equality_prefix_at(position)?;
        if endpoint.sort != anchor.endpoint.sort {
            return Err(TraceViewError::Invalid(
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
                rekeys: Box::new([]),
            }
        } else {
            self.explain_raw_equality_support_with_cutoff(
                RawEqualityEndpoint {
                    sort: endpoint.sort,
                    raw: endpoint.raw,
                },
                RawEqualityEndpoint {
                    sort: anchor.endpoint.sort,
                    raw: anchor.endpoint.raw,
                },
                equality_prefix,
            )?
        };
        let anchor = RawEqualitySupport {
            applied: Box::new([]),
            facts: Box::new([anchor.occurrence.fact]),
            rekeys: anchor.rekeys,
        };
        Ok(RawTermAvailability {
            support: combine_raw_equality_support([structural, bridge, anchor]),
            aliases: aliases.into_boxed_slice(),
        })
    }

    /// Clone one structural replay node from the shared interner.
    ///
    /// Unknown ids, including a missing sentinel used where a concrete term is
    /// required, are reported as invalid trace references.
    pub fn replay_term(&self, term: ReplayTermId) -> Result<ReplayTerm, TraceViewError> {
        self.replay_terms
            .node(term)
            .ok_or_else(|| TraceViewError::Invalid(format!("unknown replay term {term:?}")))
    }

    fn live_fact_at(
        &self,
        fact: FactId,
        position: HistoryPosition,
    ) -> Result<RawFactRecord<'a>, TraceViewError> {
        if position > self.history_boundary {
            return Err(TraceViewError::Invalid(
                "fact query exceeds the captured trace history".into(),
            ));
        }
        let record = self.fact(fact)?;
        if record.position > position {
            return Err(TraceViewError::Invalid(format!(
                "fact {fact:?} was created after {position:?}"
            )));
        }
        if let Some(removal) = self
            .arena
            .removals
            .iter()
            .find(|removal| removal.removed_fact == fact && removal.position <= position)
        {
            return Err(TraceViewError::FactNoLongerLive {
                fact,
                position,
                ended_at: removal.position,
                successor: None,
            });
        }
        Ok(record)
    }

    /// Resolve one typed fact-cell occurrence at a global history position.
    ///
    /// The result distinguishes its immutable creation endpoint from the raw
    /// endpoint current after all visible rekeys and lists those rekey
    /// positions. The fact must be live at `position`; a removal or absorbing
    /// collision returns [`TraceViewError::FactNoLongerLive`] with the event
    /// that ended the occurrence.
    pub fn fact_cell_at(
        &mut self,
        occurrence: FactCellRef,
        position: HistoryPosition,
    ) -> Result<HistoricalFactCell, TraceViewError> {
        let fact = self.live_fact_at(occurrence.fact, position)?;
        let column = occurrence.column.index();
        let sort = self
            .replay_terms
            .table_layout(fact.table)
            .ok_or(TraceViewError::UnknownTable(fact.table))?
            .get(column)
            .copied()
            .flatten()
            .ok_or_else(|| {
                TraceViewError::Invalid(format!(
                    "fact {:?} column {column} has no logical replay sort",
                    occurrence.fact
                ))
            })?;
        let term = self
            .projector
            .fact_term(occurrence.fact, column)
            .map_err(TraceViewError::Invalid)?;
        let creation_raw = *fact.values.get(column).ok_or_else(|| {
            TraceViewError::Invalid(format!("fact {:?} has no column {column}", occurrence.fact))
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
                    return Err(TraceViewError::Invalid(format!(
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
                return Err(TraceViewError::FactNoLongerLive {
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

    fn validate_history_position(&self, position: HistoryPosition) -> Result<(), TraceViewError> {
        if position > self.history_boundary {
            return Err(TraceViewError::Invalid(
                "equality query exceeds the captured trace history".into(),
            ));
        }
        Ok(())
    }
}

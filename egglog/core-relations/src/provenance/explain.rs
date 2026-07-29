//! Lazy explanations over a publication-complete execution trace.
//!
//! Equality paths and structural occurrence support are built only for cold
//! view queries; native capture never enters this module.

use super::*;

#[derive(Clone, Copy)]
struct StructuralOccurrenceLandmark {
    equality_prefix: usize,
    position: HistoryPosition,
}

fn equality_endpoint_is_carrier_owned(term: EqualityTermRef) -> bool {
    matches!(
        term,
        EqualityTermRef::Site(_)
            | EqualityTermRef::Cell {
                origin: RowOriginRef::Site(_),
                ..
            }
    )
}

impl<'a> TraceView<'a> {
    /// Explain the historical state read by one structural equality endpoint
    /// immediately before its applied event.
    ///
    /// Equality events record both the structural proposal and the native
    /// forest edge that proposal actually applied. A proposal term may already
    /// denote an older representative, so replay also needs the strictly
    /// earlier equalities that established that denotation. The event itself
    /// is deliberately outside both cutoffs and can never justify its own
    /// precondition.
    pub fn explain_equality_denotation_before(
        &mut self,
        id: AppliedEqualityId,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let (
            mut left_carrier_owned,
            mut right_carrier_owned,
            event_position,
            native_parent,
            native_child,
        ) = {
            let raw = self
                .arena
                .durable_equalities
                .get(
                    (id.get()
                        .checked_sub(1)
                        .ok_or(TraceViewError::UnknownEquality(id))?) as usize,
                )
                .and_then(Option::as_ref)
                .ok_or(TraceViewError::UnknownEquality(id))?;
            (
                equality_endpoint_is_carrier_owned(raw.proposal.left.term),
                equality_endpoint_is_carrier_owned(raw.proposal.right.term),
                raw.position,
                raw.native_parent,
                raw.native_child,
            )
        };
        let event = self.project_applied_equality(id)?;
        if matches!(&event.reason, EqualityReason::Congruence { .. }) {
            // Congruence maintenance reconstructs both parent endpoints from
            // retained rows and child support. Its dependency is prior
            // canonicalization, not an arbitrary constructor occurrence.
            left_carrier_owned = true;
            right_carrier_owned = true;
        }
        let equality_prefix = id
            .get()
            .checked_sub(1)
            .ok_or_else(|| {
                TraceViewError::Invalid("missing applied equality has no prior prefix".into())
            })?
            .try_into()
            .map_err(|_| TraceViewError::Invalid("equality prefix exceeds storage".into()))?;
        let position =
            HistoryPosition::new(event_position.get().checked_sub(1).ok_or_else(|| {
                TraceViewError::Invalid("applied equality has no pre-event history position".into())
            })?);
        if equality_prefix != self.equality_prefix_at(position)? {
            return Err(TraceViewError::Invalid(
                "applied equality does not immediately follow its derived prefix".into(),
            ));
        }
        self.validate_equality_endpoints(event.left, event.right)?;
        let left_root = self.raw_representative_at(
            RawEqualityEndpoint {
                sort: event.left.sort,
                raw: event.left.raw,
            },
            equality_prefix,
        )?;
        let right_root = self.raw_representative_at(
            RawEqualityEndpoint {
                sort: event.right.sort,
                raw: event.right.raw,
            },
            equality_prefix,
        )?;
        let roots_match_native_edge = left_root != right_root
            && ((left_root == native_parent && right_root == native_child)
                || (left_root == native_child && right_root == native_parent));
        if !roots_match_native_edge {
            return Err(TraceViewError::Invalid(format!(
                "applied equality {id:?} proposal roots {left_root:?} and {right_root:?} do not match native edge {:?} -> {:?}",
                native_child, native_parent
            )));
        }
        let explain_error = |side: &str, error: TraceViewError| {
            TraceViewError::Invalid(format!(
                "applied equality {id:?} ({:?}, roots {left_root:?}/{right_root:?}) {side} endpoint denotation failed: {error}",
                event.reason
            ))
        };
        let left_occurrence = self
            .explain_endpoint_read_at(event.left, equality_prefix, position, left_carrier_owned)
            .map_err(|error| explain_error("left", error))?;
        let left_bridge = self
            .explain_raw_equality_support_with_cutoff(
                RawEqualityEndpoint {
                    sort: event.left.sort,
                    raw: event.left.raw,
                },
                RawEqualityEndpoint {
                    sort: event.left.sort,
                    raw: left_root,
                },
                equality_prefix,
            )
            .map_err(|error| explain_error("left", error))?;
        let right_occurrence = self
            .explain_endpoint_read_at(event.right, equality_prefix, position, right_carrier_owned)
            .map_err(|error| explain_error("right", error))?;
        let right_bridge = self
            .explain_raw_equality_support_with_cutoff(
                RawEqualityEndpoint {
                    sort: event.right.sort,
                    raw: event.right.raw,
                },
                RawEqualityEndpoint {
                    sort: event.right.sort,
                    raw: right_root,
                },
                equality_prefix,
            )
            .map_err(|error| explain_error("right", error))?;
        Ok(combine_raw_equality_support([
            left_occurrence,
            left_bridge,
            right_occurrence,
            right_bridge,
        ]))
    }

    fn raw_equality_index(&mut self) -> Result<&ExplanationForest, TraceViewError> {
        if self.equality_index.is_none() {
            let mut parents = HashMap::default();
            parents.reserve(self.arena.durable_equalities.len());
            let mut previous_position = None;
            for (index, event) in self.arena.durable_equalities.iter().enumerate() {
                let event = event.as_ref().ok_or_else(|| {
                    TraceViewError::Invalid("raw applied-equality history has an ID hole".into())
                })?;
                if previous_position.is_some_and(|previous| event.position <= previous) {
                    return Err(TraceViewError::Invalid(
                        "raw applied-equality positions are not strictly increasing".into(),
                    ));
                }
                previous_position = Some(event.position);
                if event.proposal.left.sort != event.proposal.right.sort {
                    return Err(TraceViewError::Invalid(
                        "one applied equality crosses logical sorts".into(),
                    ));
                }
                let sort = event.proposal.left.sort;
                if parents
                    .insert(
                        (sort, event.native_child),
                        (
                            event.native_parent,
                            AppliedEqualityId::new(index as u64 + 1),
                        ),
                    )
                    .is_some()
                {
                    return Err(TraceViewError::Invalid(
                        "one native equality child acquired two historical parents".into(),
                    ));
                }
            }
            self.equality_index = Some(ExplanationForest { parents });
        }
        Ok(self
            .equality_index
            .as_ref()
            .expect("initialized raw equality index disappeared"))
    }

    pub fn explain_raw_equality_support_at(
        &mut self,
        left: RawEqualityEndpoint,
        right: RawEqualityEndpoint,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let equality_prefix = self.equality_prefix_at(position)?;
        self.explain_raw_equality_support_with_cutoff(left, right, equality_prefix)
    }

    pub(super) fn explain_raw_equality_support_with_cutoff(
        &mut self,
        left: RawEqualityEndpoint,
        right: RawEqualityEndpoint,
        equality_prefix: usize,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        self.raw_equality_support_if_connected_at(left, right, equality_prefix)?
            .ok_or_else(|| {
                TraceViewError::Invalid(
                    "equality endpoints were disconnected at the historical landmark".into(),
                )
            })
    }

    /// Return the historical child equalities required to replay one
    /// congruence edge between two structural calls.
    ///
    /// The applied edge records the parent equality and its cause, but the
    /// parent's congruence also depends on each unequal child pair already
    /// being equal at the recorded cutoff. Reconstruct those dependencies
    /// from the projected terms and the existing equality forest.
    pub fn explain_congruence_child_support_at(
        &mut self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let equality_prefix = self.equality_prefix_at(position)?;
        self.validate_equality_endpoints(left, right)?;
        let (
            ReplayTerm::Call {
                sort: left_sort,
                op: left_op,
                children: left_children,
            },
            ReplayTerm::Call {
                sort: right_sort,
                op: right_op,
                children: right_children,
            },
        ) = (self.replay_term(left.term)?, self.replay_term(right.term)?)
        else {
            return Err(TraceViewError::Invalid(
                "congruence equality endpoints are not structural calls".into(),
            ));
        };
        if left_sort != right_sort
            || left_op != right_op
            || left_children.len() != right_children.len()
        {
            return Err(TraceViewError::Invalid(
                "congruence equality endpoints have incompatible structure".into(),
            ));
        }
        let left_candidates =
            self.congruence_call_child_candidates(left, equality_prefix, position)?;
        let right_candidates =
            self.congruence_call_child_candidates(right, equality_prefix, position)?;
        for left_children in &left_candidates {
            for right_children in &right_candidates {
                if left_children.len() != right_children.len() {
                    continue;
                }
                let mut support = Vec::with_capacity(left_children.len());
                let mut connected = true;
                for (left_child, right_child) in left_children.iter().zip(right_children.iter()) {
                    if left_child.sort != right_child.sort {
                        connected = false;
                        break;
                    }
                    let Some(child_support) = self.raw_equality_support_if_connected_at(
                        *left_child,
                        *right_child,
                        equality_prefix,
                    )?
                    else {
                        connected = false;
                        break;
                    };
                    support.push(child_support);
                }
                if connected {
                    return Ok(combine_raw_equality_support(support));
                }
            }
        }
        Err(TraceViewError::Invalid(
            "congruence equality has no exact historically connected constructor occurrences"
                .into(),
        ))
    }

    fn congruence_call_child_candidates(
        &mut self,
        endpoint: EqualityEndpoint,
        equality_prefix: usize,
        position: HistoryPosition,
    ) -> Result<Vec<Box<[RawEqualityEndpoint]>>, TraceViewError> {
        let ReplayTerm::Call { sort, op, children } = self.replay_term(endpoint.term)? else {
            return Err(TraceViewError::Invalid(
                "congruence equality endpoint is not a structural call".into(),
            ));
        };
        let facts = self.constructor_occurrence_facts(sort, op);
        let mut candidates = Vec::new();
        for producer in facts.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if fact.position > position {
                continue;
            }
            let table = fact.table;
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&table)
                .map(|entry| entry.clone())
                .ok_or(TraceViewError::UnknownTable(table))?;
            let output = constructor.child_sorts.len();
            if output != children.len() || fact.values.len() <= output {
                return Err(TraceViewError::Invalid(format!(
                    "constructor fact {producer:?} has an invalid replay arity"
                )));
            }
            let projected = self
                .projector
                .fact_term(producer, output)
                .map_err(TraceViewError::Invalid)?;
            if projected != endpoint.term {
                continue;
            }
            if self
                .raw_equality_support_if_connected_at(
                    RawEqualityEndpoint {
                        sort,
                        raw: fact.values[output],
                    },
                    RawEqualityEndpoint {
                        sort,
                        raw: endpoint.raw,
                    },
                    equality_prefix,
                )?
                .is_none()
            {
                continue;
            }
            candidates.push(
                constructor
                    .child_sorts
                    .iter()
                    .copied()
                    .zip(fact.values.iter().copied())
                    .map(|(sort, raw)| RawEqualityEndpoint { sort, raw })
                    .collect(),
            );
        }
        if candidates.is_empty() {
            return Err(TraceViewError::Invalid(format!(
                "congruence endpoint term {:?} has no exact historical constructor occurrence",
                endpoint.term
            )));
        }
        Ok(candidates)
    }

    fn raw_equality_support_if_connected_at(
        &mut self,
        left: RawEqualityEndpoint,
        right: RawEqualityEndpoint,
        equality_prefix: usize,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        if left.sort != right.sort {
            return Err(TraceViewError::Invalid(
                "cannot explain equality across logical sorts".into(),
            ));
        }
        let cutoff = equality_prefix;
        let parents = &self.raw_equality_index()?.parents;
        let edge_is_visible = |edge: AppliedEqualityId| edge.get() as usize <= cutoff;
        let mut left_ancestors = HashMap::<Value, usize>::default();
        let mut left_edges = Vec::new();
        let mut cursor = left.raw;
        loop {
            left_ancestors.insert(cursor, left_edges.len());
            let Some((parent, edge)) = parents.get(&(left.sort, cursor)).copied() else {
                break;
            };
            if !edge_is_visible(edge) {
                break;
            }
            left_edges.push(edge);
            cursor = parent;
        }
        let mut right_edges = Vec::new();
        let mut cursor = right.raw;
        let left_depth = loop {
            if let Some(depth) = left_ancestors.get(&cursor).copied() {
                break depth;
            }
            let Some((parent, edge)) = parents.get(&(right.sort, cursor)).copied() else {
                return Ok(None);
            };
            if !edge_is_visible(edge) {
                return Ok(None);
            }
            right_edges.push(edge);
            cursor = parent;
        };
        let mut edges = left_edges[..left_depth].to_vec();
        edges.extend(right_edges);
        edges.sort_unstable();
        edges.dedup();
        Ok(Some(RawEqualitySupport {
            applied: edges.into_boxed_slice(),
            facts: Box::new([]),
            rekeys: Box::new([]),
        }))
    }

    fn raw_representative_at(
        &mut self,
        endpoint: RawEqualityEndpoint,
        equality_prefix: usize,
    ) -> Result<Value, TraceViewError> {
        let cutoff = equality_prefix;
        let parents = &self.raw_equality_index()?.parents;
        let mut cursor = endpoint.raw;
        let mut steps = 0usize;
        while let Some((parent, edge)) = parents.get(&(endpoint.sort, cursor)).copied() {
            if edge.get() as usize > cutoff {
                break;
            }
            cursor = parent;
            steps += 1;
            if steps > cutoff {
                return Err(TraceViewError::Invalid(
                    "raw applied-equality history contains a parent cycle".into(),
                ));
            }
        }
        Ok(cursor)
    }

    pub fn explain_equality_support_at(
        &mut self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let equality_prefix = self.equality_prefix_at(position)?;
        match self.observed_equality_support(left, right, equality_prefix, position)? {
            ObservedEqualitySupport::Support(support) => Ok(support),
            ObservedEqualitySupport::Missing(term) => Err(TraceViewError::Invalid(format!(
                "endpoint term {term:?} has no supported historical native occurrence"
            ))),
        }
    }

    fn observed_equality_support(
        &mut self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        equality_prefix: usize,
        position: HistoryPosition,
    ) -> Result<ObservedEqualitySupport, TraceViewError> {
        self.validate_equality_endpoints(left, right)?;
        let Some(left_support) = self.explain_endpoint_term_occurrence_if_observed(
            left,
            equality_prefix,
            position,
            true,
        )?
        else {
            return Ok(ObservedEqualitySupport::Missing(left.term));
        };
        let Some(right_support) = self.explain_endpoint_term_occurrence_if_observed(
            right,
            equality_prefix,
            position,
            true,
        )?
        else {
            return Ok(ObservedEqualitySupport::Missing(right.term));
        };
        let raw_support = if left.raw == right.raw {
            RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                rekeys: Box::new([]),
            }
        } else {
            self.explain_raw_equality_support_with_cutoff(
                RawEqualityEndpoint {
                    sort: left.sort,
                    raw: left.raw,
                },
                RawEqualityEndpoint {
                    sort: right.sort,
                    raw: right.raw,
                },
                equality_prefix,
            )?
        };
        Ok(ObservedEqualitySupport::Support(
            combine_raw_equality_support([left_support, right_support, raw_support]),
        ))
    }

    fn validate_equality_endpoints(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
    ) -> Result<(), TraceViewError> {
        if left.term.is_missing() || right.term.is_missing() {
            return Err(TraceViewError::Invalid(
                "cannot explain equality with a missing ReplayTermId".into(),
            ));
        }
        for endpoint in [left, right] {
            let node = self.replay_terms.node(endpoint.term).ok_or_else(|| {
                TraceViewError::Invalid(format!(
                    "equality endpoint owns unknown term {:?}",
                    endpoint.term
                ))
            })?;
            if node.sort() != endpoint.sort {
                return Err(TraceViewError::Invalid(
                    "equality endpoint term has the wrong logical sort".into(),
                ));
            }
        }
        if left.sort != right.sort {
            return Err(TraceViewError::Invalid(
                "cannot explain equality across logical sorts".into(),
            ));
        }
        Ok(())
    }

    fn explain_endpoint_term_occurrence(
        &mut self,
        endpoint: EqualityEndpoint,
        equality_prefix: usize,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        self.explain_endpoint_term_occurrence_if_observed(
            endpoint,
            equality_prefix,
            position,
            true,
        )?
        .ok_or_else(|| {
            TraceViewError::Invalid(format!(
                "endpoint term {:?} has no supported historical native occurrence",
                endpoint.term
            ))
        })
    }

    fn explain_endpoint_read_at(
        &mut self,
        endpoint: EqualityEndpoint,
        equality_prefix: usize,
        position: HistoryPosition,
        carrier_owned: bool,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let original = self
            .replay_terms
            .original_value(endpoint.sort, endpoint.term);
        let original_support = if let Some(original) = original {
            self.raw_equality_support_if_connected_at(
                RawEqualityEndpoint {
                    sort: endpoint.sort,
                    raw: original,
                },
                RawEqualityEndpoint {
                    sort: endpoint.sort,
                    raw: endpoint.raw,
                },
                equality_prefix,
            )?
        } else {
            None
        };
        let occurrence = self.explain_endpoint_term_occurrence_if_observed(
            endpoint,
            equality_prefix,
            position,
            !carrier_owned,
        )?;
        if carrier_owned {
            // The selected carrier constructs this endpoint. An exact older
            // occurrence contributes only its canonicalization path; the
            // occurrence fact itself is not an input. Compatible no-op
            // lookups still retain their structural anchor.
            return Ok(occurrence
                .or(original_support)
                .unwrap_or(RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([]),
                    rekeys: Box::new([]),
                }));
        }
        match (occurrence, original_support, original) {
            (Some(occurrence), _, _) => Ok(occurrence),
            (None, Some(original), _) => Ok(original),
            (None, None, Some(_)) => Err(TraceViewError::Invalid(format!(
                "endpoint term {:?} original value is disconnected from its captured proposal",
                endpoint.term
            ))),
            (None, None, None) => Err(TraceViewError::Invalid(format!(
                "endpoint term {:?} has no historical occurrence or original value",
                endpoint.term
            ))),
        }
    }

    fn explain_endpoint_term_occurrence_if_observed(
        &mut self,
        endpoint: EqualityEndpoint,
        equality_prefix: usize,
        position: HistoryPosition,
        retain_exact_producer: bool,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        match self.replay_term(endpoint.term)? {
            ReplayTerm::Literal { .. } => {
                let original = self
                    .replay_terms
                    .original_value(endpoint.sort, endpoint.term)
                    .ok_or_else(|| {
                        TraceViewError::Invalid(format!(
                            "literal endpoint term {:?} has no original native value",
                            endpoint.term
                        ))
                    })?;
                self.raw_equality_support_if_connected_at(
                    RawEqualityEndpoint {
                        sort: endpoint.sort,
                        raw: original,
                    },
                    RawEqualityEndpoint {
                        sort: endpoint.sort,
                        raw: endpoint.raw,
                    },
                    equality_prefix,
                )
            }
            ReplayTerm::Call { .. } => self.explain_term_occurrence_with_mode_at(
                endpoint.term,
                endpoint.sort,
                endpoint.raw,
                equality_prefix,
                position,
                FactId::MISSING,
                retain_exact_producer,
                0,
            ),
        }
    }

    pub fn explain_fact_cell_support_at(
        &mut self,
        left: FactCellRef,
        right: FactCellRef,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let equality_prefix = self.equality_prefix_at(position)?;
        let left = self.fact_cell_at(left, position)?;
        let right = self.fact_cell_at(right, position)?;
        if left.created.sort != right.created.sort {
            return Err(TraceViewError::Invalid(
                "cannot explain fact-cell equality across logical sorts".into(),
            ));
        }
        let support = if left.created.raw == right.created.raw
            && left.occurrence != right.occurrence
        {
            // Equal structural ids do not imply equal native occurrences:
            // delete/recreate can place one hash-consed term in two roots.
            self.explain_same_raw_fact_occurrences(&left, &right)?
        } else if left.created.raw == right.created.raw {
            self.explain_fact_term_occurrence(&left)?.ok_or_else(|| {
                TraceViewError::Invalid(format!(
                    "{} has no supported historical native occurrence",
                    self.describe_fact_cell(&left),
                ))
            })?
        } else {
            // The two exact fact cells are the structural occurrences that
            // satisfied the check.  Do not discard them and search globally
            // for another occurrence of the same ReplayTermId; retain each
            // cell's own producer, then explain only their historical native
            // connectivity.
            let left_support = self.explain_fact_term_occurrence(&left)?.ok_or_else(|| {
                TraceViewError::Invalid(format!(
                    "left {} has no supported historical native occurrence",
                    self.describe_fact_cell(&left),
                ))
            })?;
            let right_support = self.explain_fact_term_occurrence(&right)?.ok_or_else(|| {
                TraceViewError::Invalid(format!(
                    "right {} has no supported historical native occurrence",
                    self.describe_fact_cell(&right),
                ))
            })?;
            let raw_support = self.explain_raw_equality_support_with_cutoff(
                RawEqualityEndpoint {
                    sort: left.created.sort,
                    raw: left.created.raw,
                },
                RawEqualityEndpoint {
                    sort: right.created.sort,
                    raw: right.created.raw,
                },
                equality_prefix,
            )?;
            combine_raw_equality_support([left_support, right_support, raw_support])
        };
        let mut facts = vec![left.occurrence.fact, right.occurrence.fact];
        facts.extend(support.facts);
        facts.sort_unstable();
        facts.dedup();
        let mut rekeys = left.rekeys.into_vec();
        rekeys.extend(right.rekeys);
        rekeys.extend(support.rekeys);
        rekeys.sort_unstable();
        rekeys.dedup();
        Ok(RawEqualitySupport {
            applied: support.applied,
            facts: facts.into_boxed_slice(),
            rekeys: rekeys.into_boxed_slice(),
        })
    }

    pub fn explain_fact_endpoint_support_at(
        &mut self,
        fact: FactCellRef,
        endpoint: EqualityEndpoint,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let equality_prefix = self.equality_prefix_at(position)?;
        let fact = self.fact_cell_at(fact, position)?;
        if fact.created.sort != endpoint.sort {
            return Err(TraceViewError::Invalid(
                "cannot explain fact/endpoint equality across logical sorts".into(),
            ));
        }
        // Native root connectivity alone does not establish either exact
        // structural occurrence. A direct outer union can connect a fact to a
        // parent created with structurally different-but-equal children; the
        // check may then read its requested parent through a no-op canonical
        // lookup. Retain both occurrence witnesses at every raw-path shape.
        let fact_support = self.explain_fact_term_occurrence(&fact)?.ok_or_else(|| {
            TraceViewError::Invalid(format!(
                "{} has no supported historical native occurrence",
                self.describe_fact_cell(&fact),
            ))
        })?;
        let endpoint_support =
            self.explain_endpoint_term_occurrence(endpoint, equality_prefix, position)?;
        let raw_support = if fact.created.raw == endpoint.raw {
            RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                rekeys: Box::new([]),
            }
        } else {
            self.explain_raw_equality_support_with_cutoff(
                RawEqualityEndpoint {
                    sort: fact.created.sort,
                    raw: fact.created.raw,
                },
                RawEqualityEndpoint {
                    sort: endpoint.sort,
                    raw: endpoint.raw,
                },
                equality_prefix,
            )?
        };
        let support = combine_raw_equality_support([fact_support, endpoint_support, raw_support]);
        let mut facts = vec![fact.occurrence.fact];
        facts.extend(support.facts);
        facts.sort_unstable();
        facts.dedup();
        let mut rekeys = fact.rekeys.into_vec();
        rekeys.extend(support.rekeys);
        rekeys.sort_unstable();
        rekeys.dedup();
        Ok(RawEqualitySupport {
            applied: support.applied,
            facts: facts.into_boxed_slice(),
            rekeys: rekeys.into_boxed_slice(),
        })
    }

    pub(super) fn equality_prefix_at(
        &mut self,
        position: HistoryPosition,
    ) -> Result<usize, TraceViewError> {
        self.validate_history_position(position)?;
        // Building the forest validates ID density and strictly increasing
        // positions once. Every later historical cutoff is then a binary
        // search instead of another full equality-history walk.
        let _ = self.raw_equality_index()?;
        let count = self
            .arena
            .durable_equalities
            .partition_point(|event| event.as_ref().unwrap().position <= position);
        Ok(count)
    }

    fn constructor_occurrence_facts(
        &mut self,
        sort: ReplaySortId,
        op: ReplayOpId,
    ) -> Arc<[FactId]> {
        if self.constructor_occurrence_index.is_none() {
            let mut facts = HashMap::<(ReplaySortId, ReplayOpId), Vec<FactId>>::default();
            facts.reserve(self.replay_terms.table_constructors.len());
            let registered = self
                .replay_terms
                .table_constructors
                .iter()
                .map(|entry| (entry.value().result_sort, entry.value().op))
                .collect::<HashSet<_>>();
            let equality_sorts = registered.iter().map(|(sort, _)| *sort).collect();
            let mut certified_calls = HashSet::default();
            let mut visited_terms = HashSet::default();
            for recipe in self.term_recipes.rules.values() {
                for template in recipe.current_roots.iter().flatten() {
                    self.collect_certified_template_calls(
                        template,
                        &mut certified_calls,
                        &mut visited_terms,
                    );
                }
            }
            for origin in &self.term_recipes.row_origins {
                for template in origin.cells.iter().flatten() {
                    self.collect_certified_template_calls(
                        template,
                        &mut certified_calls,
                        &mut visited_terms,
                    );
                }
            }
            for origin in &self.term_recipes.term_origins {
                self.collect_certified_template_calls(
                    &origin.term,
                    &mut certified_calls,
                    &mut visited_terms,
                );
            }
            for (index, slot) in self.arena.facts.iter().enumerate() {
                let Some(fact) = slot.as_ref() else {
                    continue;
                };
                let Some(constructor) = self
                    .replay_terms
                    .table_constructors
                    .get(&fact.table)
                    .map(|entry| entry.clone())
                else {
                    continue;
                };
                facts
                    .entry((constructor.result_sort, constructor.op))
                    .or_default()
                    .push(FactId::new(index as u64 + 1));
            }
            self.constructor_occurrence_index = Some(ConstructorOccurrenceIndex {
                facts: facts
                    .into_iter()
                    .map(|(key, facts)| (key, Arc::from(facts)))
                    .collect(),
                registered,
                equality_sorts,
                certified_calls,
            });
        }
        self.constructor_occurrence_index
            .as_ref()
            .expect("initialized constructor occurrence index disappeared")
            .facts
            .get(&(sort, op))
            .cloned()
            .unwrap_or_else(|| Arc::from([]))
    }

    fn is_registered_constructor_call(&mut self, sort: ReplaySortId, op: ReplayOpId) -> bool {
        let _ = self.constructor_occurrence_facts(sort, op);
        self.constructor_occurrence_index
            .as_ref()
            .expect("initialized constructor occurrence index disappeared")
            .registered
            .contains(&(sort, op))
    }

    fn is_certified_replay_call(&mut self, sort: ReplaySortId, op: ReplayOpId) -> bool {
        let _ = self.constructor_occurrence_facts(sort, op);
        self.constructor_occurrence_index
            .as_ref()
            .expect("initialized constructor occurrence index disappeared")
            .certified_calls
            .contains(&(sort, op))
    }

    fn is_equality_sort(&mut self, sort: ReplaySortId, seed_op: ReplayOpId) -> bool {
        let _ = self.constructor_occurrence_facts(sort, seed_op);
        self.constructor_occurrence_index
            .as_ref()
            .expect("initialized constructor occurrence index disappeared")
            .equality_sorts
            .contains(&sort)
    }

    pub(super) fn explain_structural_term_availability_at(
        &mut self,
        term: ReplayTermId,
        position: HistoryPosition,
        depth: usize,
        aliases: &mut Vec<ReplayAliasPlan>,
        desired: Option<RawEqualityEndpoint>,
        anchor: Option<&HistoricalFactCell>,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        if let Some(support) = self.try_explain_structural_term_availability_at(
            term,
            position,
            depth,
            aliases,
            StructuralAvailabilityContext {
                desired,
                anchor,
                fresh_after: None,
            },
        )? {
            return Ok(support);
        }
        Err(TraceViewError::Invalid(format!(
            "structural term {term:?} ({:?}, desired {desired:?}) has no exact historical producer by {position:?}",
            self.replay_term(term)?
        )))
    }

    /// Inclusive native-history frontier of replay-visible mutations in one
    /// support set. Facts and applied equalities own allocated event positions;
    /// rekeys already carry theirs. `causes` only attribute those mutations and
    /// therefore do not add another scheduling boundary.
    fn replay_support_frontier(
        &self,
        support: &RawEqualitySupport,
    ) -> Result<HistoryPosition, TraceViewError> {
        let mut frontier = HistoryPosition::new(0);
        for equality in support.applied.iter().copied() {
            frontier = frontier.max(self.applied_equality(equality)?.position);
        }
        for fact in support.facts.iter().copied() {
            frontier = frontier.max(self.fact(fact)?.position);
        }
        for rekey in support.rekeys.iter().copied() {
            frontier = frontier.max(rekey);
        }
        Ok(frontier)
    }

    fn try_explain_structural_term_availability_at(
        &mut self,
        term: ReplayTermId,
        position: HistoryPosition,
        depth: usize,
        aliases: &mut Vec<ReplayAliasPlan>,
        context: StructuralAvailabilityContext<'_>,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        let StructuralAvailabilityContext {
            desired,
            anchor,
            fresh_after: inherited_fresh_after,
        } = context;
        if depth > 256 {
            return Err(TraceViewError::Invalid(
                "structural term availability exceeds 256 call levels".into(),
            ));
        }
        let ReplayTerm::Call { sort, op, children } = self.replay_term(term)? else {
            return Ok(Some(RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                rekeys: Box::new([]),
            }));
        };

        if !self.is_registered_constructor_call(sort, op) {
            if !self.is_certified_replay_call(sort, op) {
                return Err(TraceViewError::Invalid(format!(
                    "structural call {op:?} for {sort:?} has no replay-safe availability producer"
                )));
            }
            let equality_sort = self.is_equality_sort(sort, op);
            let mut fresh_after = inherited_fresh_after;
            let mut support_ready_after = HistoryPosition::new(0);
            if self.replay_terms.container_child_sorts.contains_key(&sort)
                && let (Some(desired), Some(anchor)) = (desired, anchor)
            {
                let versions = self.replay_terms.container_anchors(sort, desired.raw);
                if versions.len() > 1 && versions.contains(&term) {
                    let anchor_position = self.fact(anchor.occurrence.fact)?.position;
                    fresh_after = Some(
                        fresh_after.map_or(anchor_position, |current| current.max(anchor_position)),
                    );
                }
            }
            let mut parts = Vec::with_capacity(children.len() + usize::from(desired.is_some()));
            if equality_sort && let Some(desired) = desired {
                let equality_prefix = self.equality_prefix_at(position)?;
                parts.push(self.explain_pure_eqsort_call_occurrence(
                    sort,
                    &children,
                    desired.raw,
                    StructuralOccurrenceLandmark {
                        equality_prefix,
                        position,
                    },
                    true,
                    depth,
                )?);
            }
            let alias_checkpoint = aliases.len();
            for child in children.iter().copied() {
                let child_desired = match self.replay_term(child)? {
                    ReplayTerm::Call {
                        sort: child_sort,
                        op: child_op,
                        ..
                    } if self.is_equality_sort(child_sort, child_op) => self
                        .replay_terms
                        .original_value(child_sort, child)
                        .map(|raw| RawEqualityEndpoint {
                            sort: child_sort,
                            raw,
                        }),
                    ReplayTerm::Literal { .. } | ReplayTerm::Call { .. } => None,
                };
                let Some(support) = self.try_explain_structural_term_availability_at(
                    child,
                    position,
                    depth + 1,
                    aliases,
                    StructuralAvailabilityContext {
                        desired: child_desired,
                        anchor: None,
                        fresh_after,
                    },
                )?
                else {
                    aliases.truncate(alias_checkpoint);
                    return Ok(None);
                };
                support_ready_after =
                    support_ready_after.max(self.replay_support_frontier(&support)?);
                parts.push(support);
            }
            // Pure calls and the allowed ordered containers can be evaluated
            // once their child aliases and child denotation bridges are
            // available. The replay scheduler enforces both separately.
            aliases.push(ReplayAliasPlan {
                producer: None,
                ready_after: fresh_after
                    .unwrap_or(HistoryPosition::new(0))
                    .max(support_ready_after),
                fresh_after,
            });
            return Ok(Some(combine_raw_equality_support(parts)));
        }

        let possible = self.constructor_occurrence_facts(sort, op);
        // ReplayTermId identifies syntax, not one native occurrence. Prefer
        // an exact structural producer and use the historical equality
        // prefix only to bridge that occurrence to the row value requested by
        // its parent. The second pass is the narrow spelling fallback for a
        // row whose source recipe contains a pure expression but whose
        // committed child column stores the evaluated base value.
        let passes = if desired.is_some() { 2 } else { 1 };
        let equality_prefix = desired
            .map(|_| self.equality_prefix_at(position))
            .transpose()?;
        let preferred = anchor
            .filter(|anchor| anchor.occurrence.column.index() == children.len())
            .map(|anchor| anchor.occurrence.fact)
            .filter(|fact| possible.binary_search(fact).is_ok());
        for pass in 0..passes {
            for offset in 0..possible.len() + usize::from(preferred.is_some()) {
                let producer = if offset == 0
                    && let Some(preferred) = preferred
                {
                    preferred
                } else {
                    let ordinary_offset = offset - usize::from(preferred.is_some());
                    let index = if desired.is_some() {
                        ordinary_offset
                    } else {
                        possible.len() - ordinary_offset - 1
                    };
                    let producer = possible[index];
                    if Some(producer) == preferred {
                        continue;
                    }
                    producer
                };
                let fact_position = self.fact(producer)?.position;
                if fact_position > position {
                    continue;
                }
                let constructor = self
                    .replay_terms
                    .table_constructors
                    .get(&self.fact(producer)?.table)
                    .map(|entry| entry.clone())
                    .ok_or_else(|| {
                        TraceViewError::Invalid(format!(
                            "constructor occurrence {producer:?} lost its replay metadata"
                        ))
                    })?;
                let output = constructor.child_sorts.len();
                let produced_term = self
                    .projector
                    .fact_term(producer, output)
                    .map_err(TraceViewError::Invalid)?;
                let exact_term = produced_term == term;
                if (pass == 0) != exact_term {
                    continue;
                }
                let occurrence = FactCellRef {
                    fact: producer,
                    column: crate::ColumnId::from_usize(output),
                };
                let (output_cell, occurrence_position) =
                    match self.fact_cell_at(occurrence, position) {
                        Ok(cell) => (cell, position),
                        Err(TraceViewError::FactNoLongerLive { ended_at, .. }) => {
                            let last_live = ended_at.get().checked_sub(1).ok_or_else(|| {
                                TraceViewError::Invalid(format!(
                                    "constructor producer {producer:?} ended before history began"
                                ))
                            })?;
                            let last_live = HistoryPosition::new(last_live);
                            (self.fact_cell_at(occurrence, last_live)?, last_live)
                        }
                        Err(error) => return Err(error),
                    };
                // Output equivalence may be established after this exact row
                // is gone: an alias captured while live survives later unions.
                // Its key is different. Children must address the producer
                // while the row exists, so recursion uses the bounded
                // occurrence position rather than the consumer position.
                let output_support = if let Some(desired) = desired {
                    if desired.sort != output_cell.endpoint.sort {
                        continue;
                    }
                    if desired.raw == output_cell.endpoint.raw {
                        None
                    } else if exact_term || anchor.is_some() {
                        let equality_prefix = equality_prefix.expect("desired output has a prefix");
                        let created = anchor.map(|anchor| RawEqualityEndpoint {
                            sort: anchor.created.sort,
                            raw: anchor.created.raw,
                        });
                        let mut support = None;
                        let mut connected = false;
                        for target in std::iter::once(desired)
                            .chain(created.filter(|created| *created != desired))
                        {
                            if target.sort != output_cell.endpoint.sort {
                                continue;
                            }
                            if target.raw == output_cell.endpoint.raw {
                                connected = true;
                                break;
                            }
                            if let Some(candidate) = self.raw_equality_support_if_connected_at(
                                RawEqualityEndpoint {
                                    sort: output_cell.endpoint.sort,
                                    raw: output_cell.endpoint.raw,
                                },
                                target,
                                equality_prefix,
                            )? {
                                support = Some(candidate);
                                connected = true;
                                break;
                            }
                        }
                        if !connected {
                            continue;
                        }
                        support
                    } else {
                        continue;
                    }
                } else {
                    None
                };
                if children.len() != constructor.child_sorts.len() {
                    return Err(TraceViewError::Invalid(format!(
                        "constructor term {term:?} has {} children but its producer expects {}",
                        children.len(),
                        constructor.child_sorts.len()
                    )));
                }
                let mut parts = Vec::with_capacity(children.len() + 2);
                let alias_checkpoint = aliases.len();
                let mut compatible = true;
                let mut support_ready_after = HistoryPosition::new(0);
                if let Some(support) = output_support {
                    parts.push(support);
                }
                for (column, (child, child_sort)) in children
                    .iter()
                    .copied()
                    .zip(constructor.child_sorts.iter().copied())
                    .enumerate()
                {
                    let child_cell = self.fact_cell_at(
                        FactCellRef {
                            fact: producer,
                            column: crate::ColumnId::from_usize(column),
                        },
                        occurrence_position,
                    )?;
                    if child_cell.endpoint.sort != child_sort {
                        return Err(TraceViewError::Invalid(format!(
                            "constructor producer {producer:?} child {column} changed replay sort"
                        )));
                    }
                    let Some(support) = self.try_explain_structural_term_availability_at(
                        child,
                        occurrence_position,
                        depth + 1,
                        aliases,
                        StructuralAvailabilityContext {
                            desired: Some(RawEqualityEndpoint {
                                sort: child_sort,
                                raw: child_cell.endpoint.raw,
                            }),
                            anchor: Some(&child_cell),
                            fresh_after: inherited_fresh_after,
                        },
                    )?
                    else {
                        aliases.truncate(alias_checkpoint);
                        compatible = false;
                        break;
                    };
                    support_ready_after =
                        support_ready_after.max(self.replay_support_frontier(&support)?);
                    parts.push(support);
                    let child_anchor = RawEqualitySupport {
                        applied: Box::new([]),
                        facts: Box::new([child_cell.occurrence.fact]),
                        rekeys: child_cell.rekeys,
                    };
                    support_ready_after =
                        support_ready_after.max(self.replay_support_frontier(&child_anchor)?);
                    parts.push(child_anchor);
                }
                if !compatible {
                    continue;
                }
                // Capture this exact constructor occurrence as soon as its own
                // producer exists. A parent anchor is causal support for the
                // requested denotation, not liveness for the child row; using
                // its later position would cross removal/recreation and collapse
                // distinct same-syntax occurrences. Replay scheduling separately
                // waits for every child alias and key-support frontier before
                // constructing the parent.
                let available_after = fact_position;
                aliases.push(ReplayAliasPlan {
                    producer: Some(producer),
                    ready_after: inherited_fresh_after
                        .map_or(available_after, |fresh| fresh.max(available_after))
                        .max(support_ready_after),
                    fresh_after: inherited_fresh_after,
                });
                parts.push(RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    rekeys: output_cell.rekeys,
                });
                return Ok(Some(combine_raw_equality_support(parts)));
            }
        }
        Ok(None)
    }

    fn explain_pure_eqsort_call_occurrence(
        &mut self,
        result_sort: ReplaySortId,
        children: &[ReplayTermId],
        desired_raw: Value,
        landmark: StructuralOccurrenceLandmark,
        retain_exact_producer: bool,
        depth: usize,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        struct WalkContext {
            result_sort: ReplaySortId,
            desired_raw: Value,
            equality_prefix: usize,
            position: HistoryPosition,
            retain_exact_producer: bool,
        }

        fn walk(
            view: &mut TraceView<'_>,
            context: &WalkContext,
            term: ReplayTermId,
            depth: usize,
            visited: &mut HashSet<ReplayTermId>,
            supports: &mut Vec<RawEqualitySupport>,
        ) -> Result<(), TraceViewError> {
            if depth > 256 {
                return Err(TraceViewError::Invalid(
                    "pure-call occurrence explanation exceeds 256 structural levels".into(),
                ));
            }
            if !visited.insert(term) {
                return Ok(());
            }
            let ReplayTerm::Call { sort, op, children } = view.replay_term(term)? else {
                return Ok(());
            };
            if sort == context.result_sort
                && view.is_registered_constructor_call(sort, op)
                && let Some(support) = view.explain_term_occurrence_with_mode_at(
                    term,
                    sort,
                    context.desired_raw,
                    context.equality_prefix,
                    context.position,
                    FactId::MISSING,
                    context.retain_exact_producer,
                    depth + 1,
                )?
            {
                supports.push(support);
            }
            for child in children.iter().copied() {
                walk(view, context, child, depth + 1, visited, supports)?;
            }
            Ok(())
        }

        let mut visited = HashSet::default();
        let mut supports = Vec::new();
        let context = WalkContext {
            result_sort,
            desired_raw,
            equality_prefix: landmark.equality_prefix,
            position: landmark.position,
            retain_exact_producer,
        };
        for child in children.iter().copied() {
            walk(
                self,
                &context,
                child,
                depth + 1,
                &mut visited,
                &mut supports,
            )?;
        }
        if supports.is_empty() {
            return Err(TraceViewError::Invalid(format!(
                "certified pure call for {result_sort:?} has no supported same-sort constructor descendant"
            )));
        }
        Ok(combine_raw_equality_support(supports))
    }

    /// A container builder has no table FactId, but two structural container
    /// terms can denote the same registry value only because their positional
    /// EqSort children were equal when they were interned. Reconcile the
    /// requested term with every known structural anchor for that value and
    /// retain those child equalities lazily. Ordinary pure primitives do not
    /// need this step because they do not hash-cons an identity over EqSort
    /// children.
    #[allow(clippy::too_many_arguments)]
    fn explain_container_call_occurrence(
        &mut self,
        sort: ReplaySortId,
        op: ReplayOpId,
        target_children: &[ReplayTermId],
        desired_raw: Value,
        equality_prefix: usize,
        position: HistoryPosition,
        retain_exact_producer: bool,
        depth: usize,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let anchors = self.replay_terms.container_anchors(sort, desired_raw);
        let mut parts = Vec::new();
        let mut found_compatible_anchor = false;
        for candidate in anchors {
            let ReplayTerm::Call {
                sort: candidate_sort,
                op: candidate_op,
                children: candidate_children,
            } = self.replay_term(candidate)?
            else {
                continue;
            };
            if candidate_sort != sort
                || candidate_op != op
                || candidate_children.len() != target_children.len()
            {
                continue;
            }
            let mut candidate_parts = Vec::new();
            let mut compatible = true;
            for (&target_child, &candidate_child) in
                target_children.iter().zip(candidate_children.iter())
            {
                if target_child == candidate_child {
                    continue;
                }
                let target_node = self.replay_term(target_child)?;
                let candidate_node = self.replay_term(candidate_child)?;
                let child_sort = target_node.sort();
                if candidate_node.sort() != child_sort {
                    compatible = false;
                    break;
                }
                let ReplayTerm::Call { .. } = target_node else {
                    // Base literals are canonical values. Distinct literal
                    // nodes cannot explain one positional container identity.
                    compatible = false;
                    break;
                };
                let Some(candidate_raw) = self
                    .replay_terms
                    .original_value(child_sort, candidate_child)
                else {
                    compatible = false;
                    break;
                };
                let Some(target_support) = self.explain_term_occurrence_with_mode_at(
                    target_child,
                    child_sort,
                    candidate_raw,
                    equality_prefix,
                    position,
                    FactId::MISSING,
                    retain_exact_producer,
                    depth + 1,
                )?
                else {
                    compatible = false;
                    break;
                };
                // Unlike the carrier-owned target, this candidate is an
                // earlier registry anchor and its exact producer is an input.
                let Some(candidate_support) = self.explain_term_occurrence_with_mode_at(
                    candidate_child,
                    child_sort,
                    candidate_raw,
                    equality_prefix,
                    position,
                    FactId::MISSING,
                    true,
                    depth + 1,
                )?
                else {
                    compatible = false;
                    break;
                };
                // The target establishes why the source child could be read
                // at this registry value; the candidate establishes the
                // historical anchor that made the no-op container lookup hit.
                // Keeping only the former loses zero-edge constructor
                // attachments such as A/Alias and makes replay mint a
                // different container identity.
                candidate_parts.push(target_support);
                candidate_parts.push(candidate_support);
            }
            if compatible {
                found_compatible_anchor = true;
                parts.extend(candidate_parts);
            }
        }
        if !found_compatible_anchor {
            return Err(TraceViewError::Invalid(format!(
                "container call {op:?} for {sort:?} has no compatible structural anchor at {desired_raw:?}"
            )));
        }
        Ok(combine_raw_equality_support(parts))
    }

    fn producer_output_support(
        &mut self,
        producer: FactId,
        output: usize,
        sort: ReplaySortId,
        desired_raw: Value,
        equality_prefix: usize,
        position: HistoryPosition,
    ) -> Result<Option<(HistoricalFactCell, RawEqualitySupport)>, TraceViewError> {
        let output_cell = match self.fact_cell_at(
            FactCellRef {
                fact: producer,
                column: crate::ColumnId::from_usize(output),
            },
            position,
        ) {
            Ok(cell) => cell,
            Err(TraceViewError::FactNoLongerLive { .. }) => return Ok(None),
            Err(error) => return Err(error),
        };
        let output_support = match self.explain_raw_equality_support_with_cutoff(
            RawEqualityEndpoint {
                sort,
                raw: output_cell.created.raw,
            },
            RawEqualityEndpoint {
                sort,
                raw: desired_raw,
            },
            equality_prefix,
        ) {
            Ok(support) => support,
            Err(TraceViewError::Invalid(message))
                if message == "equality endpoints were disconnected at the historical landmark" =>
            {
                return Ok(None);
            }
            Err(error) => return Err(error),
        };
        Ok(Some((output_cell, output_support)))
    }

    /// Retain every exact structural occurrence connected to `desired_raw`
    /// at this landmark. Replay aliases name structural terms, not native
    /// occurrence IDs, so a hash-consed term that was created in multiple
    /// native components must keep every connected creator and the bridges
    /// between them. This is deliberately cold and only runs for selected
    /// structural terms.
    fn explain_exact_term_occurrences_at(
        &mut self,
        term: ReplayTermId,
        sort: ReplaySortId,
        desired_raw: Value,
        equality_prefix: usize,
        position: HistoryPosition,
        excluded_fact: FactId,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        let query = StructuralOccurrenceQuery {
            term,
            sort,
            raw: desired_raw,
            position,
            excluded_fact,
            retain_exact_producer: true,
        };
        if let Some(cached) = self.exact_occurrence_support_cache.get(&query) {
            return Ok(cached.clone());
        }
        let ReplayTerm::Call {
            sort: term_sort,
            op,
            ..
        } = self.replay_term(term)?
        else {
            let support = RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                rekeys: Box::new([]),
            };
            self.exact_occurrence_support_cache
                .insert(query, Some(support.clone()));
            return Ok(Some(support));
        };
        if term_sort != sort {
            return Err(TraceViewError::Invalid(
                "exact occurrence term has the wrong logical sort".into(),
            ));
        }

        let possible = self.constructor_occurrence_facts(sort, op);
        let mut supports = Vec::new();
        let mut first_projection_error = None;
        for producer in possible.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if producer == excluded_fact || fact.position > position {
                continue;
            }
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
                .ok_or(TraceViewError::UnknownTable(fact.table))?;
            let output = constructor.child_sorts.len();
            let produced_term = match self.projector.fact_term(producer, output) {
                Ok(term) => term,
                Err(error) => {
                    first_projection_error.get_or_insert(error);
                    continue;
                }
            };
            if produced_term != term {
                continue;
            }
            let creation_raw = *fact.values.get(output).ok_or_else(|| {
                TraceViewError::Invalid(format!(
                    "constructor fact {producer:?} has no output column {output}"
                ))
            })?;
            let raw_support = match self.explain_raw_equality_support_with_cutoff(
                RawEqualityEndpoint {
                    sort,
                    raw: creation_raw,
                },
                RawEqualityEndpoint {
                    sort,
                    raw: desired_raw,
                },
                equality_prefix,
            ) {
                Ok(support) => support,
                Err(TraceViewError::Invalid(message))
                    if message
                        == "equality endpoints were disconnected at the historical landmark" =>
                {
                    continue;
                }
                Err(error) => return Err(error),
            };
            supports.push(combine_raw_equality_support([
                raw_support,
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    rekeys: Box::new([]),
                },
            ]));
        }
        if supports.is_empty() {
            if let Some(error) = first_projection_error {
                return Err(TraceViewError::Invalid(error));
            }
            self.exact_occurrence_support_cache.insert(query, None);
            return Ok(None);
        }
        let support = combine_raw_equality_support(supports);
        self.exact_occurrence_support_cache
            .insert(query, Some(support.clone()));
        Ok(Some(support))
    }

    fn explain_fact_term_occurrence(
        &mut self,
        cell: &HistoricalFactCell,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        let fact = self.fact(cell.occurrence.fact)?;
        let schema = self.table_schema(fact.table)?;
        if cell.occurrence.column.index() >= schema.key_columns
            && schema.kind == ReplayTableKind::Constructor
        {
            return Ok(Some(RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([cell.occurrence.fact]),
                rekeys: Box::new([]),
            }));
        }
        if matches!(
            self.replay_term(cell.created.term)?,
            ReplayTerm::Literal { .. }
        ) {
            return Ok(Some(RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([cell.occurrence.fact]),
                rekeys: Box::new([]),
            }));
        }
        let origin =
            self.exact_fact_cell_origin(cell.occurrence.fact, cell.occurrence.column.index(), 0)?;
        let origin = RawEqualitySupport {
            applied: Box::new([]),
            facts: Box::new([origin]),
            rekeys: Box::new([]),
        };
        let equality_prefix = self.equality_prefix_at(fact.position)?;
        let structural = self.explain_term_occurrence_with_prefix_at(
            cell.created.term,
            cell.created.sort,
            cell.created.raw,
            equality_prefix,
            fact.position,
            cell.occurrence.fact,
        )?;
        Ok(Some(match structural {
            Some(structural) => combine_raw_equality_support([structural, origin]),
            None => origin,
        }))
    }

    fn exact_fact_cell_origin(
        &self,
        fact: FactId,
        column: usize,
        depth: usize,
    ) -> Result<FactId, TraceViewError> {
        if depth > 256 {
            return Err(TraceViewError::Invalid(
                "fact-cell structural origin exceeds 256 links".into(),
            ));
        }
        let record = self
            .arena
            .facts
            .get(
                (fact.get().checked_sub(1).ok_or_else(|| {
                    TraceViewError::Invalid("missing FactId has no structural origin".into())
                })?) as usize,
            )
            .and_then(Option::as_ref)
            .ok_or(TraceViewError::UnknownFact(fact))?;
        match record.origin {
            Some(FactOrigin::Site(_)) => Ok(fact),
            Some(FactOrigin::Fact(source)) => {
                self.exact_fact_cell_origin(source, column, depth + 1)
            }
            Some(FactOrigin::Merge {
                incoming,
                prior,
                cells,
            }) => {
                let cell = *self
                    .arena
                    .durable_merge_cell_origins
                    .get(cells.as_range())
                    .and_then(|cells| cells.get(column))
                    .ok_or_else(|| {
                        TraceViewError::Invalid(format!(
                            "merge origin for {fact:?} has no column {column}"
                        ))
                    })?;
                match cell {
                    MergeCellOrigin::Incoming(source) => match incoming {
                        Some(RowOriginRef::Site(_)) => Ok(fact),
                        Some(RowOriginRef::Fact(source_fact)) => {
                            self.exact_fact_cell_origin(source_fact, source as usize, depth + 1)
                        }
                        None => Err(TraceViewError::Invalid(format!(
                            "merge origin for {fact:?} lost incoming column {column}"
                        ))),
                    },
                    MergeCellOrigin::Prior(source) => {
                        self.exact_fact_cell_origin(prior, source as usize, depth + 1)
                    }
                    MergeCellOrigin::Unsupported => Err(TraceViewError::Invalid(format!(
                        "merge origin for {fact:?} synthesized column {column}"
                    ))),
                }
            }
            None => Err(TraceViewError::Invalid(format!(
                "fact {fact:?} column {column} has no structural origin"
            ))),
        }
    }

    /// Explain how one structural Call could be read at `desired_raw` without
    /// trusting final `(sort, value)` state. Exact producer facts are the base
    /// case. A constructor lookup that was a native no-op is reconstructed
    /// against a live compatible producer row, recursively retaining the
    /// child equalities that made its canonical key hit that row. This is a
    /// cold fact-graph walk over retained terms, not rule matching or replay.
    #[cfg(test)]
    pub(crate) fn explain_term_occurrence_at(
        &mut self,
        term: ReplayTermId,
        sort: ReplaySortId,
        desired_raw: Value,
        position: HistoryPosition,
        excluded_fact: FactId,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        let equality_prefix = self.equality_prefix_at(position)?;
        self.explain_term_occurrence_with_prefix_at(
            term,
            sort,
            desired_raw,
            equality_prefix,
            position,
            excluded_fact,
        )
    }

    fn explain_term_occurrence_with_prefix_at(
        &mut self,
        term: ReplayTermId,
        sort: ReplaySortId,
        desired_raw: Value,
        equality_prefix: usize,
        position: HistoryPosition,
        excluded_fact: FactId,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        self.explain_term_occurrence_with_mode_at(
            term,
            sort,
            desired_raw,
            equality_prefix,
            position,
            excluded_fact,
            true,
            0,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn explain_term_occurrence_with_mode_at(
        &mut self,
        term: ReplayTermId,
        sort: ReplaySortId,
        desired_raw: Value,
        equality_prefix: usize,
        position: HistoryPosition,
        excluded_fact: FactId,
        retain_exact_producer: bool,
        depth: usize,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        if depth > 256 {
            return Err(TraceViewError::Invalid(
                "structural occurrence explanation exceeds 256 constructor levels".into(),
            ));
        }
        let ReplayTerm::Call {
            sort: term_sort,
            op,
            children: target_children,
        } = self.replay_term(term)?
        else {
            return Ok(None);
        };
        if term_sort != sort {
            return Err(TraceViewError::Invalid(
                "structural occurrence term has the wrong logical sort".into(),
            ));
        }
        let query = StructuralOccurrenceQuery {
            term,
            sort,
            raw: desired_raw,
            position,
            excluded_fact,
            retain_exact_producer,
        };
        if let Some(cached) = self.occurrence_support_cache.get(&query) {
            return Ok(cached.clone());
        }

        // Production Call nodes have exactly two origins: registered table
        // constructors, or frontend-certified pure primitives with validators.
        // The latter are recomputed by `let-check` and deliberately have no
        // constructor FactId of their own. Ordered container builders are the
        // one structural exception: their identity depends on positional
        // EqSort children, so reconcile those child equalities through the
        // container anchor index before treating the call as available.
        if !self.is_registered_constructor_call(sort, op) {
            if !self.is_certified_replay_call(sort, op) {
                return Err(TraceViewError::Invalid(format!(
                    "structural call {op:?} for {sort:?} has no registered constructor or certified replay recipe"
                )));
            }
            let support = if self.replay_terms.container_child_sorts.contains_key(&sort) {
                self.explain_container_call_occurrence(
                    sort,
                    op,
                    &target_children,
                    desired_raw,
                    equality_prefix,
                    position,
                    retain_exact_producer,
                    depth,
                )?
            } else if self.is_equality_sort(sort, op) {
                self.explain_pure_eqsort_call_occurrence(
                    sort,
                    &target_children,
                    desired_raw,
                    StructuralOccurrenceLandmark {
                        equality_prefix,
                        position,
                    },
                    retain_exact_producer,
                    depth,
                )?
            } else {
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([]),
                    rekeys: Box::new([]),
                }
            };
            self.occurrence_support_cache
                .insert(query, Some(support.clone()));
            return Ok(Some(support));
        }

        let possible = self.constructor_occurrence_facts(sort, op);
        let sibling_cause = (!excluded_fact.is_missing())
            .then(|| self.fact(excluded_fact).map(|fact| fact.cause))
            .transpose()?;
        // Prefer an exact producer occurrence. This is the overwhelmingly
        // common path and needs no recursive child reconciliation. Iterate
        // newest-first because it is usually closest to the consumer's
        // historical landmark and therefore has the shortest raw path.
        for producer in possible.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if producer == excluded_fact {
                continue;
            }
            let later_sibling = fact.position > position && Some(fact.cause) == sibling_cause;
            if fact.position > position && !later_sibling {
                continue;
            }
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
                .ok_or(TraceViewError::UnknownTable(fact.table))?;
            let output = constructor.child_sorts.len();
            let produced_term = self
                .projector
                .fact_term(producer, output)
                .map_err(TraceViewError::Invalid)?;
            if produced_term != term {
                continue;
            }
            let output_support = if later_sibling {
                let creation_raw = *fact.values.get(output).ok_or_else(|| {
                    TraceViewError::Invalid(format!(
                        "constructor fact {producer:?} has no output column {output}"
                    ))
                })?;
                let support = match self.explain_raw_equality_support_with_cutoff(
                    RawEqualityEndpoint {
                        sort,
                        raw: creation_raw,
                    },
                    RawEqualityEndpoint {
                        sort,
                        raw: desired_raw,
                    },
                    equality_prefix,
                ) {
                    Ok(support) => support,
                    Err(TraceViewError::Invalid(message))
                        if message
                            == "equality endpoints were disconnected at the historical landmark" =>
                    {
                        continue;
                    }
                    Err(error) => return Err(error),
                };
                (support, Vec::new().into_boxed_slice())
            } else {
                let Some((output_cell, support)) = self.producer_output_support(
                    producer,
                    output,
                    sort,
                    desired_raw,
                    equality_prefix,
                    position,
                )?
                else {
                    continue;
                };
                (support, output_cell.rekeys)
            };
            let support = if retain_exact_producer {
                combine_raw_equality_support([
                    output_support.0,
                    RawEqualitySupport {
                        applied: Box::new([]),
                        facts: Box::new([producer]),
                        rekeys: output_support.1,
                    },
                ])
            } else {
                output_support.0
            };
            self.occurrence_support_cache
                .insert(query, Some(support.clone()));
            return Ok(Some(support));
        }

        // A successful constructor lookup may have inserted nothing because
        // canonicalized children hit a compatible older row. Reconstruct
        // only that case, recursively, and stop at the first exact support;
        // slicing needs a sound witness, not a minimum one.
        for producer in possible.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if producer == excluded_fact || fact.position > position {
                continue;
            }
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
                .ok_or(TraceViewError::UnknownTable(fact.table))?;
            let output = constructor.child_sorts.len();
            let produced_term = self
                .projector
                .fact_term(producer, output)
                .map_err(TraceViewError::Invalid)?;
            let ReplayTerm::Call {
                sort: produced_sort,
                op: produced_op,
                children: produced_children,
            } = self.replay_term(produced_term)?
            else {
                continue;
            };
            if produced_sort != sort
                || produced_op != op
                || produced_children.len() != target_children.len()
            {
                continue;
            }
            let Some((output_cell, output_support)) = self.producer_output_support(
                producer,
                output,
                sort,
                desired_raw,
                equality_prefix,
                position,
            )?
            else {
                continue;
            };
            let mut parts = vec![
                output_support,
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    rekeys: output_cell.rekeys,
                },
            ];
            let mut compatible = true;
            for (column, (&target_child, &produced_child)) in target_children
                .iter()
                .zip(produced_children.iter())
                .enumerate()
            {
                if target_child == produced_child {
                    continue;
                }
                let target_node = self.replay_term(target_child)?;
                let produced_node = self.replay_term(produced_child)?;
                let (
                    ReplayTerm::Call {
                        sort: child_sort, ..
                    },
                    ReplayTerm::Call {
                        sort: produced_child_sort,
                        ..
                    },
                ) = (&target_node, &produced_node)
                else {
                    compatible = false;
                    break;
                };
                if child_sort != produced_child_sort
                    || constructor.child_sorts.get(column) != Some(child_sort)
                {
                    compatible = false;
                    break;
                }
                let child_cell = match self.fact_cell_at(
                    FactCellRef {
                        fact: producer,
                        column: crate::ColumnId::from_usize(column),
                    },
                    position,
                ) {
                    Ok(cell) => cell,
                    Err(TraceViewError::FactNoLongerLive { .. }) => {
                        compatible = false;
                        break;
                    }
                    Err(error) => return Err(error),
                };
                let child_support = self.explain_term_occurrence_with_mode_at(
                    target_child,
                    *child_sort,
                    child_cell.endpoint.raw,
                    equality_prefix,
                    position,
                    producer,
                    retain_exact_producer,
                    depth + 1,
                )?;
                let Some(mut child_support) = child_support else {
                    compatible = false;
                    break;
                };
                let mut rekeys = child_support.rekeys.into_vec();
                rekeys.extend(child_cell.rekeys);
                child_support.rekeys = rekeys.into_boxed_slice();
                parts.push(child_support);
            }
            if !compatible {
                continue;
            }
            let support = combine_raw_equality_support(parts);
            self.occurrence_support_cache
                .insert(query, Some(support.clone()));
            return Ok(Some(support));
        }
        self.occurrence_support_cache.insert(query, None);
        Ok(None)
    }

    fn explain_equal_term_child_occurrences(
        &mut self,
        cell: &HistoricalFactCell,
    ) -> Result<Option<RawEqualitySupport>, TraceViewError> {
        let ReplayTerm::Call { sort, op, children } = self.replay_term(cell.created.term)? else {
            return Ok(None);
        };
        let position = self.fact(cell.occurrence.fact)?.position;
        let equality_prefix = self.equality_prefix_at(position)?;
        let possible = self.constructor_occurrence_facts(sort, op);
        let mut first_projection_error = None;
        for producer in possible.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if producer == cell.occurrence.fact || fact.position > position {
                continue;
            }
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
                .ok_or(TraceViewError::UnknownTable(fact.table))?;
            let output = constructor.child_sorts.len();
            let produced_term = match self.projector.fact_term(producer, output) {
                Ok(term) => term,
                Err(error) => {
                    first_projection_error.get_or_insert(error);
                    continue;
                }
            };
            if produced_term != cell.created.term {
                continue;
            }
            let Some((output_cell, output_support)) = self.producer_output_support(
                producer,
                output,
                sort,
                cell.created.raw,
                equality_prefix,
                position,
            )?
            else {
                continue;
            };
            let mut parts = vec![
                output_support,
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    rekeys: output_cell.rekeys,
                },
            ];
            for (column, (&child, &child_sort)) in children
                .iter()
                .zip(constructor.child_sorts.iter())
                .enumerate()
            {
                let child_cell = self.fact_cell_at(
                    FactCellRef {
                        fact: producer,
                        column: crate::ColumnId::from_usize(column),
                    },
                    position,
                )?;
                if let Some(mut support) = self.explain_exact_term_occurrences_at(
                    child,
                    child_sort,
                    child_cell.endpoint.raw,
                    equality_prefix,
                    position,
                    producer,
                )? {
                    let mut rekeys = support.rekeys.into_vec();
                    rekeys.extend(child_cell.rekeys);
                    support.rekeys = rekeys.into_boxed_slice();
                    parts.push(support);
                }
            }
            return Ok(Some(combine_raw_equality_support(parts)));
        }
        if let Some(error) = first_projection_error {
            return Err(TraceViewError::Invalid(error));
        }
        Ok(None)
    }

    fn explain_same_raw_fact_occurrences(
        &mut self,
        left: &HistoricalFactCell,
        right: &HistoricalFactCell,
    ) -> Result<RawEqualitySupport, TraceViewError> {
        let left_support = match self.explain_fact_term_occurrence(left)? {
            Some(support) => support,
            None => {
                return Err(TraceViewError::Invalid(format!(
                    "left {} has no supported historical native occurrence",
                    self.describe_fact_cell(left),
                )));
            }
        };
        let right_support = match self.explain_fact_term_occurrence(right)? {
            Some(support) => support,
            None => {
                return Err(TraceViewError::Invalid(format!(
                    "right {} has no supported historical native occurrence",
                    self.describe_fact_cell(right),
                )));
            }
        };
        let mut parts = vec![left_support, right_support];
        if left.created.term == right.created.term {
            if let Some(support) = self.explain_equal_term_child_occurrences(left)? {
                parts.push(support);
            }
            if let Some(support) = self.explain_equal_term_child_occurrences(right)? {
                parts.push(support);
            }
        }
        Ok(combine_raw_equality_support(parts))
    }

    fn describe_fact_cell(&self, cell: &HistoricalFactCell) -> String {
        let fallback = || {
            format!(
                "fact cell {:?}:{} term {:?} at raw {:?}",
                cell.occurrence.fact,
                cell.occurrence.column.index(),
                cell.created.term,
                cell.created.raw,
            )
        };
        let Ok(fact) = self.fact(cell.occurrence.fact) else {
            return fallback();
        };
        let Ok(schema) = self.table_schema(fact.table) else {
            return fallback();
        };
        let Ok(term) = self.replay_term(cell.created.term) else {
            return fallback();
        };
        format!(
            "fact cell {:?}:{} in table {:?} ({:?}, {} key columns), term {:?}={term:?} at raw {:?}, created at {:?}, cause {:?}, row {:?}",
            cell.occurrence.fact,
            cell.occurrence.column.index(),
            fact.table,
            schema.kind,
            schema.key_columns,
            cell.created.term,
            cell.created.raw,
            fact.position,
            fact.cause,
            fact.values,
        )
    }
}

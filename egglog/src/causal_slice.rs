use std::collections::VecDeque;

use crate::core_relations::{
    AppliedEqualityId, CausalReceiptView, CheckEndpointOccurrence, EqualityEdgeCount,
    EqualityEndpoint, EqualityReason, FactCellRef, FactId, HistoryPosition,
    ProjectedAppliedEquality, RawEqualityEndpoint, RawEqualitySupport, RawReceiptCause,
    ReceiptCausePrior, ReceiptCauseRef, ReceiptEqualitySource, ReceiptViewError, ReplayTermId,
    RuleMatchId, SourceRef,
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
    pub(crate) facts: HashSet<FactId>,
    pub(crate) matches: HashSet<RuleMatchId>,
    pub(crate) equalities: HashSet<AppliedEqualityId>,
    pub(crate) rekeys: HashSet<HistoryPosition>,
    pub(crate) causes: HashSet<ReceiptCauseRef>,
    pub(crate) sources: HashSet<SourceRef>,
    pub(crate) fact_terms: HashMap<FactId, Box<[ReplayTermId]>>,
    pub(crate) match_terms: HashMap<RuleMatchId, Box<[ReplayTermId]>>,
    pub(crate) equality_records: HashMap<AppliedEqualityId, ProjectedAppliedEquality>,
    requirements: Vec<SupportRequirement>,
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

fn slice_view(
    view: &mut CausalReceiptView<'_>,
    check: u32,
) -> Result<CausalSlice, ReceiptViewError> {
    let root = view.check_root(check)?.clone();
    let mut slice = CausalSlice::default();
    slice.checks.insert(check);
    let mut work = VecDeque::new();
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
        enqueue_support(&mut slice, &mut work, support);
    }

    while let Some(item) = work.pop_front() {
        match item {
            Work::Fact(id) => {
                if !slice.facts.insert(id) {
                    continue;
                }
                let cause = view.fact(id)?.cause;
                let terms = view.fact_terms(id)?;
                slice.fact_terms.insert(id, terms);
                work.push_back(Work::Cause(cause));
            }
            Work::Matched(id) => {
                if !slice.matches.insert(id) {
                    continue;
                }
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
                    let support =
                        explain_rule_equality(view, left, right, &premises, as_of_edges, position)?;
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
                        slice.sources.insert(source.clone());
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
    slice
        .validate_exact_support()
        .map_err(|error| ReceiptViewError::Invalid(error.to_string()))?;
    Ok(slice)
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
                    view.explain_equality_support_at(left, right, root.as_of_edges, root.position);
                assert!(matches!(
                    generic,
                    Err(ReceiptViewError::Invalid(message))
                        if message.contains("requires exact occurrence provenance")
                ));
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

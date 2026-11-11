use std::{
    collections::VecDeque,
    sync::atomic::{AtomicU32, Ordering},
};

use crossbeam_queue::SegQueue;

use crate::{
    TableId, Value,
    common::{HashMap, HashSet},
    numeric_id::NumericId,
};

use super::{AtomId, RuleMatchId};

#[derive(Clone, Debug)]
pub(crate) struct CompactTableCommit {
    pub row: Box<[Value]>,
    pub cause: RuleMatchId,
}

/// One exact native table row used by a compact rule receipt.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReceiptFact {
    pub table: TableId,
    pub row: Box<[Value]>,
}

/// A run-local identity for a fact recorded by [`CompactReceipts`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ReceiptFactId(u32);

impl ReceiptFactId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PendingReceiptMatch {
    pub id: RuleMatchId,
    pub rule: u32,
    pub premises: Box<[ReceiptFact]>,
}

/// One promoted native rule match. Matches with no effective commit are absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompactRuleReceipt {
    pub id: RuleMatchId,
    /// Run-local action identity. A bridge integration must replace this with a
    /// source-stable rule token before receipts cross databases.
    pub rule: u32,
    pub premises: Box<[ReceiptFactId]>,
}

/// One effective committed fact and the match that produced it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompactFactReceipt {
    pub fact: ReceiptFact,
    pub cause: Option<RuleMatchId>,
}

/// One applied native union. Redundant union proposals are deliberately absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompactUnionReceipt {
    pub lhs: Value,
    pub rhs: Value,
    pub cause: RuleMatchId,
}

/// Backward-reachable support from one committed fact or equality observation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CompactReceiptSlice {
    pub facts: Vec<ReceiptFactId>,
    pub matches: Vec<RuleMatchId>,
    pub source_facts: Vec<ReceiptFactId>,
}

/// Compact, native, one-wave receipt graph.
///
/// This diagnostic representation stores exact native rows, not named
/// bindings or proof syntax. It intentionally has no cross-wave or decomposed
/// materialization contract yet.
#[derive(Clone, Debug, Default)]
pub struct CompactReceipts {
    pub facts: Vec<CompactFactReceipt>,
    pub matches: Vec<CompactRuleReceipt>,
    pub unions: Vec<CompactUnionReceipt>,
    pub pending_matches: usize,
}

impl CompactReceipts {
    pub fn fact_id(&self, table: TableId, row: &[Value]) -> Option<ReceiptFactId> {
        self.facts
            .iter()
            .position(|fact| fact.fact.table == table && fact.fact.row.as_ref() == row)
            .map(|index| ReceiptFactId(u32::try_from(index).unwrap()))
    }

    pub fn backward_from_fact(&self, root: ReceiptFactId) -> CompactReceiptSlice {
        self.backward_from_seeds([root], [])
    }

    pub fn backward_from_equality(&self, lhs: Value, rhs: Value) -> Option<CompactReceiptSlice> {
        if lhs == rhs {
            return Some(CompactReceiptSlice::default());
        }
        let mut adjacency = HashMap::<Value, Vec<(Value, RuleMatchId)>>::default();
        for edge in &self.unions {
            adjacency
                .entry(edge.lhs)
                .or_default()
                .push((edge.rhs, edge.cause));
            adjacency
                .entry(edge.rhs)
                .or_default()
                .push((edge.lhs, edge.cause));
        }
        let mut queue = VecDeque::from([lhs]);
        let mut previous = HashMap::<Value, (Value, RuleMatchId)>::default();
        let mut seen = HashSet::default();
        seen.insert(lhs);
        while let Some(current) = queue.pop_front() {
            for &(next, cause) in adjacency.get(&current).into_iter().flatten() {
                if !seen.insert(next) {
                    continue;
                }
                previous.insert(next, (current, cause));
                if next == rhs {
                    let mut matches = Vec::new();
                    let mut cursor = rhs;
                    while cursor != lhs {
                        let (prior, cause) = previous[&cursor];
                        matches.push(cause);
                        cursor = prior;
                    }
                    return Some(self.backward_from_seeds([], matches));
                }
                queue.push_back(next);
            }
        }
        None
    }

    fn backward_from_seeds(
        &self,
        facts: impl IntoIterator<Item = ReceiptFactId>,
        matches: impl IntoIterator<Item = RuleMatchId>,
    ) -> CompactReceiptSlice {
        let match_map = self
            .matches
            .iter()
            .map(|receipt| (receipt.id, receipt))
            .collect::<HashMap<_, _>>();
        let mut fact_work = facts.into_iter().collect::<Vec<_>>();
        let mut match_work = matches.into_iter().collect::<Vec<_>>();
        let mut reached_facts = HashSet::default();
        let mut reached_matches = HashSet::default();
        let mut source_facts = HashSet::default();
        while let Some(fact) = fact_work.pop() {
            if !reached_facts.insert(fact) {
                continue;
            }
            match self.facts[fact.index()].cause {
                Some(cause) => match_work.push(cause),
                None => {
                    source_facts.insert(fact);
                }
            }
        }
        while let Some(cause) = match_work.pop() {
            if !reached_matches.insert(cause) {
                continue;
            }
            if let Some(receipt) = match_map.get(&cause) {
                fact_work.extend(receipt.premises.iter().copied());
            }
            while let Some(fact) = fact_work.pop() {
                if !reached_facts.insert(fact) {
                    continue;
                }
                match self.facts[fact.index()].cause {
                    Some(parent) => match_work.push(parent),
                    None => {
                        source_facts.insert(fact);
                    }
                }
            }
        }
        let mut facts = reached_facts.into_iter().collect::<Vec<_>>();
        let mut matches = reached_matches.into_iter().collect::<Vec<_>>();
        let mut source_facts = source_facts.into_iter().collect::<Vec<_>>();
        facts.sort();
        matches.sort_by_key(|id| id.index());
        source_facts.sort();
        CompactReceiptSlice {
            facts,
            matches,
            source_facts,
        }
    }

    pub(crate) fn from_effects(
        pending: Vec<PendingReceiptMatch>,
        fact_effects: Vec<(TableId, Box<[Value]>, RuleMatchId)>,
        unions: Vec<CompactUnionReceipt>,
    ) -> Self {
        let pending_matches = pending.len();
        let pending = pending
            .into_iter()
            .map(|receipt| (receipt.id, receipt))
            .collect::<HashMap<_, _>>();
        let promoted = fact_effects
            .iter()
            .map(|(_, _, cause)| *cause)
            .chain(unions.iter().map(|edge| edge.cause))
            .collect::<HashSet<_>>();
        let mut facts = Vec::<CompactFactReceipt>::new();
        let mut fact_ids = HashMap::<ReceiptFact, ReceiptFactId>::default();
        let mut intern = |fact: ReceiptFact, cause: Option<RuleMatchId>| {
            if let Some(id) = fact_ids.get(&fact).copied() {
                if facts[id.index()].cause.is_none() && cause.is_some() {
                    facts[id.index()].cause = cause;
                }
                return id;
            }
            let id = ReceiptFactId(u32::try_from(facts.len()).unwrap());
            fact_ids.insert(fact.clone(), id);
            facts.push(CompactFactReceipt { fact, cause });
            id
        };
        let mut matches = Vec::with_capacity(promoted.len());
        for id in promoted.iter().copied() {
            let Some(pending) = pending.get(&id) else {
                continue;
            };
            let premises = pending
                .premises
                .iter()
                .cloned()
                .map(|fact| intern(fact, None))
                .collect::<Vec<_>>()
                .into_boxed_slice();
            matches.push(CompactRuleReceipt {
                id,
                rule: pending.rule,
                premises,
            });
        }
        for (table, row, cause) in fact_effects {
            intern(ReceiptFact { table, row }, Some(cause));
        }
        matches.sort_by_key(|receipt| receipt.id.index());
        Self {
            facts,
            matches,
            unions,
            pending_matches,
        }
    }
}

#[derive(Default)]
pub(crate) struct CompactRunRecorder {
    next_match: AtomicU32,
    pending: SegQueue<PendingReceiptMatch>,
}

impl CompactRunRecorder {
    pub(crate) fn capture(
        &self,
        rule: usize,
        premises: impl IntoIterator<Item = (AtomId, ReceiptFact)>,
    ) -> RuleMatchId {
        let id = RuleMatchId::from_index(self.next_match.fetch_add(1, Ordering::Relaxed) as usize);
        let mut premises = premises.into_iter().collect::<Vec<_>>();
        premises.sort_by_key(|(atom, _)| atom.index());
        self.pending.push(PendingReceiptMatch {
            id,
            rule: u32::try_from(rule).expect("action id should fit in u32"),
            premises: premises
                .into_iter()
                .map(|(_, fact)| fact)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        });
        id
    }

    pub(crate) fn finish(&self) -> Vec<PendingReceiptMatch> {
        let mut result = Vec::new();
        while let Some(receipt) = self.pending.pop() {
            result.push(receipt);
        }
        result
    }
}

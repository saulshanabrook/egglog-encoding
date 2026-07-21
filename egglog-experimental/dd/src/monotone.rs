//! History-sensitive operators that carry egglog's MONOTONE-FIRE semantics
//! on top of DD's view maintenance (see docs/rebuild-in-dataflow.md): rule
//! consequences persist after their trigger rows disappear (`(delete ...)`
//! is data, not view retraction), a remove-then-reinsert refires, and fresh
//! ids must be replay-stable so retraction deltas cancel exactly.
//!
//! Both operators apply each timestamp's NET delta in ascending `Ord` order
//! (timely `Product` times derive a lexicographic `Ord` refining the lattice
//! order) before acting, so they run both at the outer epoch timestamp and
//! inside `iterate` scopes; the latter additionally relies on the backend's
//! external epoch drive fully draining one epoch before feeding the next.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

use differential_dataflow::lattice::Lattice;
use differential_dataflow::{AsCollection, VecCollection};
use timely::dataflow::channels::pact::Pipeline;
use timely::dataflow::operators::generic::operator::Operator;
use timely::dataflow::operators::CapabilitySet;
use timely::progress::Timestamp;

/// One `+1` event per 0→positive transition of each datum's running count;
/// silence on falling edges. Output is append-only (monotone).
pub fn rising_edge<'scope, T, D>(coll: &VecCollection<'scope, T, D>) -> VecCollection<'scope, T, D>
where
    T: Timestamp + Lattice + Ord,
    D: differential_dataflow::ExchangeData + std::hash::Hash,
{
    let stream = coll.inner.clone().unary_frontier(
        Pipeline,
        "RisingEdge",
        move |default_cap, _info| {
            let mut caps = CapabilitySet::from_elem(default_cap);
            let mut queue: BinaryHeap<Reverse<(T, D, isize)>> = BinaryHeap::new();
            let mut counts: HashMap<D, isize> = HashMap::new();
            move |(input, frontier), output| {
                input.for_each(|_cap, data| {
                    for (d, t, r) in data.drain(..) {
                        queue.push(Reverse((t, d, r)));
                    }
                });
                // Process each COMPLETE timestamp (frontier has passed it) in
                // ascending order: apply the net delta per datum, then emit on
                // 0→positive transitions only.
                while queue
                    .peek()
                    .is_some_and(|Reverse((t, _, _))| !frontier.frontier().less_equal(t))
                {
                    let time = queue.peek().expect("peeked above").0 .0.clone();
                    let mut net: HashMap<D, isize> = HashMap::new();
                    while queue.peek().is_some_and(|Reverse((t, _, _))| *t == time) {
                        let Reverse((_, d, r)) = queue.pop().expect("peeked above");
                        *net.entry(d).or_insert(0) += r;
                    }
                    let cap = caps.delayed(&time);
                    let mut session = output.session(&cap);
                    for (d, dr) in net {
                        if dr == 0 {
                            continue;
                        }
                        let before = counts.get(&d).copied().unwrap_or(0);
                        let after = before + dr;
                        if before <= 0 && after > 0 {
                            session.give((d.clone(), time.clone(), 1isize));
                        }
                        if after == 0 {
                            counts.remove(&d);
                        } else {
                            counts.insert(d, after);
                        }
                    }
                }
                caps.downgrade(&frontier.frontier());
            }
        },
    );
    stream.as_collection()
}

/// Append-only `key -> id` dictionary: mints `counter++` the first time a key
/// is demanded (net-positive delta, dictionary miss) and emits the mapping as
/// a never-retracted `(key, id)` event; replays and re-demands return the
/// existing mapping by emitting nothing new. Negative deltas neither mint nor
/// retract.
pub fn memoizing_mint<'scope, T, K>(
    demand: &VecCollection<'scope, T, K>,
    first_id: u32,
) -> VecCollection<'scope, T, (K, u32)>
where
    T: Timestamp + Lattice + Ord,
    K: differential_dataflow::ExchangeData + std::hash::Hash,
{
    let stream = demand.inner.clone().unary_frontier(
        Pipeline,
        "MemoizingMint",
        move |default_cap, _info| {
            let mut caps = CapabilitySet::from_elem(default_cap);
            let mut queue: BinaryHeap<Reverse<(T, K, isize)>> = BinaryHeap::new();
            let mut dict: HashMap<K, u32> = HashMap::new();
            let mut counter = first_id;
            move |(input, frontier), output| {
                input.for_each(|_cap, data| {
                    for (k, t, r) in data.drain(..) {
                        queue.push(Reverse((t, k, r)));
                    }
                });
                while queue
                    .peek()
                    .is_some_and(|Reverse((t, _, _))| !frontier.frontier().less_equal(t))
                {
                    let time = queue.peek().expect("peeked above").0 .0.clone();
                    let mut net: HashMap<K, isize> = HashMap::new();
                    while queue.peek().is_some_and(|Reverse((t, _, _))| *t == time) {
                        let Reverse((_, k, r)) = queue.pop().expect("peeked above");
                        *net.entry(k).or_insert(0) += r;
                    }
                    let cap = caps.delayed(&time);
                    let mut session = output.session(&cap);
                    // Deterministic id assignment: mint in key order within
                    // each timestamp (net is a HashMap; its order is not).
                    let mut fresh: Vec<K> = net
                        .into_iter()
                        .filter(|&(ref k, dr)| dr > 0 && !dict.contains_key(k))
                        .map(|(k, _)| k)
                        .collect();
                    fresh.sort();
                    for k in fresh {
                        let id = counter;
                        counter += 1;
                        dict.insert(k.clone(), id);
                        session.give(((k, id), time.clone(), 1isize));
                    }
                }
                caps.downgrade(&frontier.frontier());
            }
        },
    );
    stream.as_collection()
}


//! Prototype of the two history-sensitive operators that carry egglog's
//! MONOTONE-FIRE semantics on top of DD's view maintenance (see
//! docs/rebuild-in-dataflow.md):
//!
//! - [`rising_edge`]: emits ONE effect event per 0→positive transition of a
//!   binding's count, and nothing on falling edges. egglog's `(delete ...)`
//!   is data, not view retraction: a match's consequences persist after the
//!   trigger row disappears, and a remove-then-reinsert must refire. Plain DD
//!   derivation would retract the consequences; this operator latches them.
//! - [`memoizing_mint`]: an append-only `key -> id` dictionary minting from a
//!   counter on first sight and returning the SAME id on any replay, so
//!   retraction deltas cancel exactly and counter-id parity is preserved.
//!   The mapping is never retracted (egglog term relations are write-only).
//!
//! Both operators apply each timestamp's NET delta in ascending timestamp
//! order before detecting transitions. The prototype runs at a totally
//! ordered epoch timestamp (`u32`); using them inside `iterate` scopes
//! (partially ordered `Product` times) additionally relies on the backend's
//! external epoch drive fully draining one epoch before feeding the next.
//!
//! The test models the smallest interesting rule, `A(x) => B(x, fresh!)`:
//! deleting `A(1)` must NOT remove `B`'s row, and re-inserting `A(1)` must
//! refire the rule but mint the SAME id.

use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::rc::Rc;

use differential_dataflow::input::Input;
use differential_dataflow::{AsCollection, VecCollection};
use timely::dataflow::channels::pact::Pipeline;
use timely::dataflow::operators::generic::operator::Operator;
use timely::dataflow::operators::probe::Handle as ProbeHandle;
use timely::dataflow::operators::CapabilitySet;
use differential_dataflow::lattice::Lattice;
use timely::progress::Timestamp;

/// One `+1` event per 0→positive transition of each datum's running count;
/// silence on falling edges. Output is append-only (monotone).
fn rising_edge<'scope, T, D>(coll: &VecCollection<'scope, T, D>) -> VecCollection<'scope, T, D>
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
fn memoizing_mint<'scope, T, K>(
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

/// Per-epoch captured deltas of a collection.
type Captured<D> = Rc<RefCell<Vec<(D, isize)>>>;

fn capture<'scope, T, D>(coll: &VecCollection<'scope, T, D>) -> Captured<D>
where
    T: Timestamp + Lattice + Ord,
    D: differential_dataflow::ExchangeData,
{
    let buf: Captured<D> = Rc::new(RefCell::new(Vec::new()));
    let buf_in = Rc::clone(&buf);
    coll.clone().inspect_batch(move |_t, batch| {
        buf_in
            .borrow_mut()
            .extend(batch.iter().map(|(d, _t, w)| (d.clone(), *w)));
    });
    buf
}

/// `A(x) => B(x, fresh!)` under monotone-fire semantics, across four epochs:
/// insert, delete (B persists), re-insert (refire, same id), and a no-op.
#[test]
fn delete_is_data_and_reinsert_refires_with_the_same_id() {
    use timely::communication::allocator::thread::Thread;
    use timely::communication::allocator::Allocator;
    use timely::worker::Worker;
    use timely::WorkerConfig;

    let alloc = Allocator::Thread(Thread::default());
    let mut worker = Worker::new(
        WorkerConfig::default(),
        alloc,
        Some(std::time::Instant::now()),
    );

    let probe = ProbeHandle::new();
    let (mut a_in, fired_buf, b_buf) = {
        let probe = probe.clone();
        worker.dataflow::<u32, _, _>(|scope| {
            let (a_in, a) = scope.new_collection::<u32, isize>();

            // The rule body is just A(x); its match collection is `a` itself.
            // Head: fire once per rising edge, mint B's fresh id per x.
            let fired = rising_edge(&a);
            let minted = memoizing_mint(&fired, 100);
            // B's rows: every firing joined with the (append-only) mapping.
            // `distinct` collapses repeated firings of the same binding.
            let fired_buf = capture(&fired);
            let b = fired
                .map(|x| (x, ()))
                .join_map(minted, |&x, &(), &id| (x, id))
                .distinct();

            let b_buf = capture(&b);
            b.probe_with(&probe);
            (a_in, fired_buf, b_buf)
        })
    };

    // (input deltas for A, expected fired events, expected net B state)
    type Epoch = (Vec<(u32, isize)>, Vec<(u32, isize)>, Vec<(u32, u32)>);
    let mut b_state: std::collections::BTreeMap<(u32, u32), isize> = Default::default();
    let epochs: Vec<Epoch> = vec![
        // Epoch 0: A(1), A(2) inserted -> both fire, ids 100 and 101.
        (
            vec![(1, 1), (2, 1)],
            vec![(1, 1), (2, 1)],
            vec![(1, 100), (2, 101)],
        ),
        // Epoch 1: delete A(1). NO falling-edge event; B keeps BOTH rows.
        (vec![(1, -1)], vec![], vec![(1, 100), (2, 101)]),
        // Epoch 2: re-insert A(1): refires (rising edge) but mints NOTHING
        // new — B still holds (1, 100) with the ORIGINAL id.
        (vec![(1, 1)], vec![(1, 1)], vec![(1, 100), (2, 101)]),
        // Epoch 3: idle.
        (vec![], vec![], vec![(1, 100), (2, 101)]),
    ];

    for (epoch, (inserts, expected_fired, expected_b)) in epochs.into_iter().enumerate() {
        for (x, w) in inserts {
            a_in.update(x, w);
        }
        let next = epoch as u32 + 1;
        a_in.advance_to(next);
        a_in.flush();
        worker.step_while(|| probe.less_than(&next));

        let mut fired: Vec<(u32, isize)> = fired_buf.borrow_mut().drain(..).collect();
        fired.sort();
        assert_eq!(fired, expected_fired, "fired events at epoch {epoch}");

        for ((x, id), w) in b_buf.borrow_mut().drain(..) {
            *b_state.entry((x, id)).or_insert(0) += w;
        }
        let b_now: Vec<(u32, u32)> = b_state
            .iter()
            .filter(|(_, &w)| w != 0)
            .map(|(&row, &w)| {
                assert_eq!(w, 1, "B rows must stay set-like");
                row
            })
            .collect();
        assert_eq!(b_now, expected_b, "B table state at epoch {epoch}");
    }
}

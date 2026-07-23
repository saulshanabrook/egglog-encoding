//! Feasibility prototype for the FlowLog-style re-architecture (task #12): does
//! running a saturation loop in a nested `iterate` scope keep its internal
//! remove/reinsert CHURN out of the downstream operators that read its result?
//!
//! This is the crux of the engine's herbie blow-up. Our current engine runs
//! every rule's join at one FLAT timestamp, so when the rebuild saturation
//! rewrites a row (delete old, insert canonical) every round, all ~130 user
//! rules' joins re-process each intermediate delta — measured at 67M match
//! deltas for 172K real emits. FlowLog avoids this by rendering recursion as a
//! nested `iterate` scope: the churn lives at inner timestamps and, on the way
//! back to the outer scope, `consolidate` nets the cancelling ±1s away, so a
//! downstream stratum sees only the per-epoch NET.
//!
//! The prototype propagates min-labels over union edges to a fixpoint (the same
//! computation as egglog's union-find leader = component minimum), which churns
//! hard: `label(5)` walks 5→4→3→2→1 across iterations. It then feeds the result
//! to a downstream join (a stand-in "user rule") and counts how many
//! `(id, label)` tuples that join ever RECEIVES. With `consolidate` after the
//! loop the count is the net (one row per id); without it, the count includes
//! every intermediate label — the churn we need to suppress.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use differential_dataflow::input::Input;
use differential_dataflow::operators::iterate::Iterate;
use timely::dataflow::operators::probe::Handle as ProbeHandle;

/// Run min-label propagation over `edges` (undirected) seeded by `ids`, feed the
/// fixpoint into a downstream `join` (labels ⋈ labels on the label value, a
/// stand-in for a user rule reading rebuild's output), and return
/// `(net label map, downstream tuples received)`. `consolidate` toggles the
/// `.consolidate()` we would insert after the loop leaves its scope.
fn run(ids: Vec<u32>, edges: Vec<(u32, u32)>, consolidate: bool) -> (BTreeMap<u32, u32>, usize) {
    use timely::communication::allocator::thread::Thread;
    use timely::communication::allocator::Allocator;
    use timely::worker::Worker;
    use timely::WorkerConfig;

    let labels_out: Rc<RefCell<Vec<((u32, u32), isize)>>> = Rc::default();
    // Total tuples the downstream join receives (with multiplicity), i.e. how
    // much churn leaks past the loop boundary.
    let downstream_recv: Rc<RefCell<usize>> = Rc::default();

    let alloc = Allocator::Thread(Thread::default());
    let mut worker = Worker::new(
        WorkerConfig::default(),
        alloc,
        Some(std::time::Instant::now()),
    );

    let (ids_in, edges_in) = {
        let labels_out = Rc::clone(&labels_out);
        let downstream_recv = Rc::clone(&downstream_recv);
        let probe = ProbeHandle::new();
        let (mut ids_in, mut edges_in) = worker.dataflow::<u32, _, _>(|scope| {
            let (ids_in, ids) = scope.new_collection::<u32, isize>();
            let (edges_in, edges) = scope.new_collection::<(u32, u32), isize>();

            // Undirected edges for propagation.
            let edges = edges.flat_map(|(a, b)| [(a, b), (b, a)]);

            // Fixpoint: label(x) = min(x, labels of neighbours). Nested iterate
            // scope — intermediate labels live at inner timestamps.
            let labels = ids.clone().map(|x| (x, x)).iterate(|scope, labels| {
                let edges = edges.enter(scope);
                let ids = ids.enter(scope);
                // Candidate labels reaching x from a neighbour y.
                let proposed = edges
                    .map(|(x, y)| (y, x))
                    .join_map(labels.clone(), |_y, &x, &label_y| (x, label_y));
                labels
                    .clone()
                    .concat(proposed)
                    .concat(ids.map(|x| (x, x)))
                    .reduce(|_x, input, output| output.push((*input[0].0, 1)))
            });

            // The `consolidate` we would insert after `leave()` to net the
            // inner-iteration churn re-stamped onto the outer timestamp.
            let labels = if consolidate {
                labels.consolidate()
            } else {
                labels
            };

            // Downstream "user rule": join labels with themselves on the label
            // value (members sharing a leader). Count every tuple it consumes.
            let recv = Rc::clone(&downstream_recv);
            let by_label = labels
                .clone()
                .map(|(x, l)| (l, x))
                .inspect_batch(move |_t, batch| {
                    *recv.borrow_mut() += batch
                        .iter()
                        .map(|(_, _, w)| w.unsigned_abs())
                        .sum::<usize>();
                });
            // The join itself (a real downstream operator consuming the stream).
            by_label
                .clone()
                .join_map(by_label, |_l, &a, &b| (a, b))
                .probe_with(&probe);

            labels
                .inspect_batch(move |_t, batch| {
                    labels_out
                        .borrow_mut()
                        .extend(batch.iter().map(|(d, _t, w)| (*d, *w)));
                })
                .probe_with(&probe);

            (ids_in, edges_in)
        });

        for id in ids {
            ids_in.insert(id);
        }
        for e in edges {
            edges_in.insert(e);
        }
        ids_in.advance_to(1);
        edges_in.advance_to(1);
        ids_in.flush();
        edges_in.flush();
        worker.step_while(|| probe.less_than(&1));
        (ids_in, edges_in)
    };
    drop(ids_in);
    drop(edges_in);
    while worker.step() {}

    let mut net: BTreeMap<(u32, u32), isize> = BTreeMap::new();
    for (d, w) in labels_out.borrow().iter() {
        *net.entry(*d).or_insert(0) += *w;
    }
    let labels: BTreeMap<u32, u32> = net
        .into_iter()
        .filter(|(_, w)| *w != 0)
        .map(|((id, label), w)| {
            assert_eq!(w, 1, "labels must be a function: {id}->{label} weight {w}");
            (id, label)
        })
        .collect();
    let recv = *downstream_recv.borrow();
    (labels, recv)
}

/// A 5-node chain 1-2-3-4-5: all collapse to leader 1, and `label(5)` churns
/// through 5,4,3,2,1. With `consolidate`, the downstream join receives exactly
/// the net (5 rows); without it, it receives the intermediate churn too.
#[test]
fn consolidate_after_loop_hides_churn_from_downstream() {
    let ids = vec![1, 2, 3, 4, 5];
    let edges = vec![(1, 2), (2, 3), (3, 4), (4, 5)];

    let (labels_c, recv_c) = run(ids.clone(), edges.clone(), true);
    let (labels_nc, recv_nc) = run(ids, edges, false);

    // Both compute the correct fixpoint (everything → leader 1).
    let expected: BTreeMap<u32, u32> = [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1)]
        .into_iter()
        .collect();
    assert_eq!(labels_c, expected, "consolidated fixpoint");
    assert_eq!(
        labels_nc, expected,
        "non-consolidated fixpoint (same answer)"
    );

    eprintln!(
        "[prototype] downstream reception: consolidated={recv_c} churn(no-consolidate)={recv_nc}"
    );
    // The point: with consolidate the downstream join sees exactly the 5 net
    // rows; without it, it sees strictly more (the intermediate labels leak).
    assert_eq!(recv_c, 5, "consolidated: downstream receives only the net");
    assert!(
        recv_nc > recv_c,
        "without consolidate the churn leaks downstream: recv_nc={recv_nc} recv_c={recv_c}"
    );
}

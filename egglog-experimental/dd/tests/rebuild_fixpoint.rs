//! Feasibility prototype: egglog's REBUILD loop as an in-dataflow DD fixpoint.
//!
//! Today the term encoding runs rebuilding as ordinary rules driven by a host
//! `(saturate ...)` schedule: every round trips host → DD → host, re-feeding
//! deltas and re-applying merges. This test demonstrates the alternative the
//! flowlog architecture suggests: express the ENTIRE
//! union-find + congruence-closure fixpoint as ONE nested `iterate` scope, so
//! a single epoch converges it inside the dataflow.
//!
//! Formulation (one loop variable):
//!
//! - `labels(x)` — the canonical leader of id `x`, seeded as the identity.
//! - Union edges = user unions ∪ congruence collisions, where collisions are
//!   DERIVED from `labels` inside the loop: canonicalize every term row's
//!   children and eclass through `labels`; two rows agreeing on
//!   `(op, canonical children)` but with different eclass labels emit a union
//!   edge toward the smaller label (exactly the FD view's
//!   `ordering-min` merge).
//! - `labels' = min(identity, labels of union-neighbors)` — min-label
//!   propagation, whose fixpoint is the component minimum: the same leader
//!   egglog's pairwise `ordering-min/max` union-find converges to.
//!
//! Both directions of the mutual recursion (labels → collisions → edges →
//! labels) live in the loop body, so plain `Collection::iterate` suffices; no
//! host round-trips, no version bumps, no re-fed deltas. Incrementality comes
//! for free: feeding new terms/unions at a later epoch reuses all prior work.
//!
//! What this deliberately does NOT cover (see docs/rebuild-in-dataflow.md):
//! fresh-id minting (stays host-side; rebuild never mints), proof-column
//! composition (proof mode needs host prims or provenance-based
//! reconstruction), and delete/subsume cleanup (retraction weights).

use std::cell::RefCell;
use std::rc::Rc;

use differential_dataflow::input::Input;
use differential_dataflow::operators::Iterate;
use timely::dataflow::operators::probe::Handle as ProbeHandle;

/// A term row: `(op, child0, child1, eclass)`; `child1 == 0` pads unary ops
/// (ids start at 1, matching the backend's zero-padding convention).
type Term = (u32, u32, u32, u32);

/// Signed `(id, label)` deltas captured from the fixpoint's output.
type CapturedLabels = Rc<RefCell<Vec<((u32, u32), isize)>>>;

/// Run the rebuild fixpoint over id/term/union inputs across two epochs and
/// return the net `(id, label)` map observed per epoch. Uses the same
/// single-thread `Worker` construction as the backend's fused join.
fn run_fixpoint(
    epoch0: (Vec<u32>, Vec<Term>, Vec<(u32, u32)>),
    epoch1: (Vec<u32>, Vec<Term>, Vec<(u32, u32)>),
) -> Vec<std::collections::BTreeMap<u32, u32>> {
    use timely::communication::allocator::thread::Thread;
    use timely::communication::allocator::Allocator;
    use timely::worker::Worker;
    use timely::WorkerConfig;

    let captured: CapturedLabels = Rc::new(RefCell::new(Vec::new()));
    let captured_in = Rc::clone(&captured);
    let mut epochs_out = Vec::new();

    let alloc = Allocator::Thread(Thread::default());
    let mut worker = Worker::new(
        WorkerConfig::default(),
        alloc,
        Some(std::time::Instant::now()),
    );
    {
        let probe = ProbeHandle::new();
        let (mut ids_in, mut terms_in, mut unions_in) = worker.dataflow::<u32, _, _>(|scope| {
            let (ids_in, ids) = scope.new_collection::<u32, isize>();
            let (terms_in, terms) = scope.new_collection::<Term, isize>();
            let (unions_in, unions) = scope.new_collection::<(u32, u32), isize>();

            let labels = ids.clone().map(|x| (x, x)).iterate(|scope, inner| {
                let ids = ids.enter(scope);
                let terms = terms.enter(scope);
                let user_unions = unions.enter(scope);

                // Canonicalize each term row's children and eclass through the
                // current labels: (op, c0, c1, e) -> ((op, l0, l1), le).
                let canon = terms
                    .map(|(op, c0, c1, e)| (c0, (op, c1, e)))
                    .join_map(inner.clone(), |_c0, &(op, c1, e), &l0| (c1, (op, l0, e)))
                    .join_map(inner.clone(), |_c1, &(op, l0, e), &l1| (e, (op, l0, l1)))
                    .join_map(inner.clone(), |_e, &(op, l0, l1), &le| ((op, l0, l1), le));

                // Congruence: rows agreeing on (op, canonical children) with
                // distinct eclass labels are equal — union every extra label
                // into the smallest (the FD view's ordering-min merge).
                let congruence_unions = canon
                    .reduce(|_key, input, output| {
                        let leader = *input[0].0;
                        for (label, _) in &input[1..] {
                            output.push(((**label, leader), 1));
                        }
                    })
                    .map(|(_key, edge)| edge);

                // Min-label propagation over user ∪ congruence union edges.
                let edges = user_unions
                    .concat(congruence_unions)
                    .flat_map(|(a, b)| [(a, b), (b, a)]);
                let candidates = edges
                    .map(|(x, y)| (y, x))
                    .join_map(inner.clone(), |_y, &x, &label_of_y| (x, label_of_y));

                inner
                    .concat(candidates)
                    .concat(ids.map(|x| (x, x)))
                    .reduce(|_x, input, output| output.push((*input[0].0, 1)))
            });

            labels
                .inspect_batch(move |_t, batch| {
                    captured_in
                        .borrow_mut()
                        .extend(batch.iter().map(|(d, _t, w)| (*d, *w)));
                })
                .probe_with(&probe);

            (ids_in, terms_in, unions_in)
        });

        let mut state: std::collections::BTreeMap<(u32, u32), isize> = Default::default();
        for (epoch, (ids, terms, unions)) in [epoch0, epoch1].into_iter().enumerate() {
            for id in ids {
                ids_in.insert(id);
            }
            for t in terms {
                terms_in.insert(t);
            }
            for u in unions {
                unions_in.insert(u);
            }
            let next = epoch as u32 + 1;
            ids_in.advance_to(next);
            terms_in.advance_to(next);
            unions_in.advance_to(next);
            ids_in.flush();
            terms_in.flush();
            unions_in.flush();
            worker.step_while(|| probe.less_than(&next));

            for ((id, label), w) in captured.borrow_mut().drain(..) {
                *state.entry((id, label)).or_insert(0) += w;
            }
            let snapshot: std::collections::BTreeMap<u32, u32> = state
                .iter()
                .filter(|(_, &w)| w != 0)
                .map(|(&(id, label), &w)| {
                    assert_eq!(w, 1, "labels must be a function: {id} -> {label} has weight {w}");
                    (id, label)
                })
                .collect();
            epochs_out.push(snapshot);
        }
    }

    epochs_out
}

const F: u32 = 100;
const G: u32 = 200;

/// Union a≡b must congruence-close f(a)≡f(b) and then g(f(a))≡g(f(b)) inside
/// ONE epoch — the nested fixpoint does the whole rebuild without host rounds.
#[test]
fn congruence_closure_converges_in_one_epoch() {
    // ids: 0 pad, 1=a, 2=b, 3=f(a), 4=f(b), 5=g(f(a)), 6=g(f(b))
    let ids = vec![0, 1, 2, 3, 4, 5, 6];
    let terms = vec![(F, 1, 0, 3), (F, 2, 0, 4), (G, 3, 0, 5), (G, 4, 0, 6)];
    let unions = vec![(1, 2)];

    let epochs = run_fixpoint((ids, terms, unions), (vec![], vec![], vec![]));

    let expected: std::collections::BTreeMap<u32, u32> =
        [(0, 0), (1, 1), (2, 1), (3, 3), (4, 3), (5, 5), (6, 5)]
            .into_iter()
            .collect();
    assert_eq!(epochs[0], expected, "two congruence levels resolve in epoch 0");
    assert_eq!(epochs[1], expected, "an empty delta epoch changes nothing");
}

/// A later epoch's delta (a new term over an existing class plus a union)
/// updates only the affected labels — the fixpoint is incremental across
/// epochs, unlike the host-driven rebuild which re-feeds version bumps.
#[test]
fn incremental_epoch_extends_the_fixpoint() {
    let ids = vec![0, 1, 2, 3, 4];
    let terms = vec![(F, 1, 0, 3), (F, 2, 0, 4)];

    // Epoch 0: nothing unified. Epoch 1: add g-terms over BOTH f-classes and
    // union a≡b: congruence must cascade through both levels incrementally.
    let epochs = run_fixpoint(
        (ids, terms, vec![]),
        (
            vec![5, 6],
            vec![(G, 3, 0, 5), (G, 4, 0, 6)],
            vec![(1, 2)],
        ),
    );

    let expected0: std::collections::BTreeMap<u32, u32> =
        [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)].into_iter().collect();
    let expected1: std::collections::BTreeMap<u32, u32> =
        [(0, 0), (1, 1), (2, 1), (3, 3), (4, 3), (5, 5), (6, 5)]
            .into_iter()
            .collect();
    assert_eq!(epochs[0], expected0);
    assert_eq!(epochs[1], expected1);
}

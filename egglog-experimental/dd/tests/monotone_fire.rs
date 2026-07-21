//! Monotone-fire semantics via `monotone::{rising_edge, memoizing_mint}`,
//! at the outer epoch timestamp. The test models the smallest interesting
//! rule, `A(x) => B(x, fresh!)`: deleting `A(1)` must NOT remove `B`'s row,
//! and re-inserting `A(1)` must refire the rule but mint the SAME id.

use std::cell::RefCell;
use std::rc::Rc;

use differential_dataflow::input::Input;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::VecCollection;
use egglog_experimental_dd::monotone::{memoizing_mint, rising_edge};
use timely::dataflow::operators::probe::Handle as ProbeHandle;
use timely::progress::Timestamp;

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

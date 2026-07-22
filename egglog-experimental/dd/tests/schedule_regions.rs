//! Prototype of the two schedule-region mechanisms the general
//! schedule -> dataflow compiler needs beyond plain `Saturate` fixpoints
//! (docs/rebuild-in-dataflow.md):
//!
//! - **`(run N)` as gated feedback**: a `Variable` loop whose feedback is
//!   filtered to rounds `< N`, so the region iterates at most N times inside
//!   ONE epoch, with early convergence for free — reproducing the frontend's
//!   bounded loop exactly.
//! - **Minting inside a saturation scope**: `monotone::memoizing_mint` runs
//!   at `Product` timestamps (their derived lexicographic `Ord` refines the
//!   lattice order for frontier-complete times), assigning ids in round order
//!   as the fixpoint grows, stable across later epochs.
//!
//! The workload is a successor chain: `A(x), Succ(x, y) => A(y)` — the
//! dataflow analog of `(run N)` / `(saturate)` over one rule.

use std::cell::RefCell;
use std::rc::Rc;

use differential_dataflow::input::Input;
use differential_dataflow::operators::iterate::Variable;
use differential_dataflow::AsCollection;
use egglog_experimental_dd::monotone::memoizing_mint;
use timely::dataflow::operators::probe::Handle as ProbeHandle;
use timely::dataflow::operators::vec::Filter;
use timely::order::Product;

fn worker() -> timely::worker::Worker {
    use timely::communication::allocator::thread::Thread;
    use timely::communication::allocator::Allocator;
    use timely::worker::Worker;
    use timely::WorkerConfig;
    Worker::new(
        WorkerConfig::default(),
        Allocator::Thread(Thread::default()),
        Some(std::time::Instant::now()),
    )
}

type Captured<D> = Rc<RefCell<Vec<(D, isize)>>>;

/// Reachable set of `seed` through `succ`, iterated at most `bound` times
/// (`None` = saturate). One epoch = the WHOLE bounded/saturating region.
fn run_region(
    succ_edges: Vec<(u32, u32)>,
    seed: Vec<u32>,
    bound: Option<u64>,
) -> (Vec<u32>, Vec<(u32, u32)>) {
    let mut worker = worker();
    let probe = ProbeHandle::new();
    let a_buf: Captured<u32> = Rc::new(RefCell::new(Vec::new()));
    let mint_buf: Captured<(u32, u32)> = Rc::new(RefCell::new(Vec::new()));

    let (mut seed_in, mut succ_in) = {
        let probe = probe.clone();
        let a_buf = Rc::clone(&a_buf);
        let mint_buf = Rc::clone(&mint_buf);
        worker.dataflow::<u32, _, _>(move |scope| {
            let (seed_in, seed) = scope.new_collection::<u32, isize>();
            let (succ_in, succ) = scope.new_collection::<(u32, u32), isize>();

            let (a, minted) = scope.scoped::<Product<u32, u64>, _, _>("Region", |inner| {
                let seed = seed.enter(inner);
                let succ = succ.enter(inner);
                let step = Product::new(Default::default(), 1);
                let (var, a) = Variable::new(inner, step);

                let grown = a.clone().map(|x| (x, ())).join_map(succ, |_x, &(), &y| y);
                let next = seed.concat(grown).distinct();

                // Mint an id for every member of the region's growing set —
                // the analog of a rule head's fresh-id demand inside the loop.
                let minted = memoizing_mint(&next, 100);

                // `(run N)`: feed back only derivations from rounds < N, so
                // the loop performs at most N bounded hops. `(saturate)`:
                // unbounded feedback.
                let fed_back = match bound {
                    Some(n) => next
                        .inner
                        .clone()
                        .filter(move |(_, t, _)| t.inner < n)
                        .as_collection(),
                    None => next.clone(),
                };
                var.set(fed_back);
                (next.leave(scope), minted.leave(scope))
            });

            let a_sink = a_buf;
            a.inspect_batch(move |_t, batch| {
                a_sink
                    .borrow_mut()
                    .extend(batch.iter().map(|(d, _t, w)| (*d, *w)));
            });
            let mint_sink = mint_buf;
            minted
                .inspect_batch(move |_t, batch| {
                    mint_sink
                        .borrow_mut()
                        .extend(batch.iter().map(|(d, _t, w)| (*d, *w)));
                })
                .probe_with(&probe);
            (seed_in, succ_in)
        })
    };

    for x in seed {
        seed_in.insert(x);
    }
    for e in succ_edges {
        succ_in.insert(e);
    }
    seed_in.advance_to(1);
    succ_in.advance_to(1);
    seed_in.flush();
    succ_in.flush();
    worker.step_while(|| probe.less_than(&1));

    let mut reachable: Vec<u32> = net_state(&a_buf);
    reachable.sort_unstable();
    let mut minted: Vec<(u32, u32)> = net_state(&mint_buf);
    minted.sort_unstable();
    (reachable, minted)
}

fn net_state<D: Ord + Clone + std::hash::Hash + Eq>(buf: &Captured<D>) -> Vec<D> {
    let mut net: std::collections::HashMap<D, isize> = Default::default();
    for (d, w) in buf.borrow_mut().drain(..) {
        *net.entry(d).or_insert(0) += w;
    }
    net.into_iter()
        .filter(|(_, w)| *w != 0)
        .map(|(d, w)| {
            assert_eq!(w, 1, "region outputs must stay set-like");
            d
        })
        .collect()
}

const CHAIN: [(u32, u32); 10] = [
    (0, 1),
    (1, 2),
    (2, 3),
    (3, 4),
    (4, 5),
    (5, 6),
    (6, 7),
    (7, 8),
    (8, 9),
    (9, 10),
];

/// `(run 3)`: exactly three bounded hops inside one epoch, matching the
/// frontend's `Repeat(3, Run)` loop over the same rule.
#[test]
fn run_n_is_gated_feedback() {
    let (reachable, _) = run_region(CHAIN.to_vec(), vec![0], Some(3));
    assert_eq!(reachable, vec![0, 1, 2, 3]);
}

/// A bound past convergence behaves like saturation (early stop for free).
#[test]
fn run_n_stops_early_at_fixpoint() {
    let (reachable, _) = run_region(CHAIN.to_vec(), vec![0], Some(50));
    assert_eq!(reachable, (0..=10).collect::<Vec<u32>>());
}

/// `(saturate)`: unbounded feedback reaches the chain's end.
#[test]
fn saturate_is_unbounded_feedback() {
    let (reachable, _) = run_region(CHAIN.to_vec(), vec![0], None);
    assert_eq!(reachable, (0..=10).collect::<Vec<u32>>());
}

/// Fresh ids minted INSIDE the saturation scope: assigned in round order as
/// the fixpoint grows (deterministic), one per distinct key.
#[test]
fn minting_inside_saturation_is_deterministic() {
    let (_, minted) = run_region(CHAIN.to_vec(), vec![0], None);
    // A(k) first appears at round k, so ids follow the chain order.
    let expected: Vec<(u32, u32)> = (0..=10).map(|k| (k, 100 + k)).collect();
    assert_eq!(minted, expected);
}

/// The gate caps minting too: only members reached within N rounds get ids.
#[test]
fn gated_region_mints_only_what_it_reaches() {
    let (_, minted) = run_region(CHAIN.to_vec(), vec![0], Some(3));
    let expected: Vec<(u32, u32)> = (0..=3).map(|k| (k, 100 + k)).collect();
    assert_eq!(minted, expected);
}

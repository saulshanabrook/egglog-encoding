use std::sync::Mutex;

use rand::{Rng, SeedableRng, rngs::SmallRng};

use super::*;

fn v(n: usize) -> Value {
    Value::from_usize(n)
}

/// A tiny checked equality algebra. Unlike an uninterpreted ID counter, it
/// catches incorrect symmetry, composition order, and pre/post-union roots.
#[derive(Default)]
struct Reasons(Mutex<Vec<(Value, Value)>>);

impl Reasons {
    fn assert(&self, a: Value, b: Value) -> Value {
        let mut reasons = self.0.lock().unwrap();
        let id = v(reasons.len());
        reasons.push((a, b));
        id
    }
    fn endpoints(&self, reason: Value) -> (Value, Value) {
        self.0.lock().unwrap()[reason.index()]
    }
}

impl ReasonComposer for Reasons {
    fn compose(&self, steps: &[ReasonStep], _: &mut ExecutionState) -> Value {
        assert!(!steps.is_empty());
        let mut result = None;
        for step in steps {
            let (mut a, mut b) = self.endpoints(step.reason);
            if step.reversed {
                std::mem::swap(&mut a, &mut b);
            }
            result = Some(match result {
                None => (a, b),
                Some((start, end)) => {
                    assert_eq!(end, a, "non-composable proof path");
                    (start, b)
                }
            });
        }
        let (a, b) = result.unwrap();
        self.assert(a, b)
    }
}

#[test]
fn explanations_survive_compression_and_old_root_queries() {
    empty_execution_state!(state);
    let reasons = Arc::new(Reasons::default());
    let mut uf = ExplainedUfTable::new(Some(reasons.clone()));
    for (a, b) in [(8, 5), (7, 3), (8, 7), (2, 5), (8, 2)] {
        uf.new_buffer()
            .stage_insert(&[v(a), v(b), reasons.assert(v(a), v(b)), v(0)]);
        uf.merge(&mut state);
        for event in &uf.events {
            assert_eq!(
                reasons.endpoints(event.link_reason),
                (event.loser, event.winner)
            );
        }
        for value in [2, 3, 5, 7, 8] {
            let value = v(value);
            if let Some(reason) = uf.canonical_reason(value, &mut state) {
                assert_eq!(reasons.endpoints(reason), (value, uf.find(value)));
            }
        }
    }
    assert_eq!(uf.len(), 4, "redundant assertions do not publish events");
    assert_eq!(uf.find(v(8)), v(2));
    let old_path = uf.explain_to(v(8), v(5)).unwrap();
    assert_eq!(
        reasons.endpoints(reasons.compose(&old_path, &mut state)),
        (v(8), v(5))
    );
    assert!(uf.explain_to(v(5), v(8)).is_none());
    assert_eq!(
        uf.get_row(&[v(8)]).unwrap().vals[1],
        v(5),
        "relational links are immutable"
    );
}

#[test]
fn random_sparse_unions_match_reference_and_have_valid_reasons() {
    empty_execution_state!(state);
    let reasons = Arc::new(Reasons::default());
    let mut uf = ExplainedUfTable::new(Some(reasons.clone()));
    let mut rng = SmallRng::seed_from_u64(127);
    let mut groups: Vec<usize> = (0..100).collect();
    let value = |i| v(1_000_000 + i * 100_003);
    for timestamp in 0..500 {
        let a = rng.random_range(0..groups.len());
        let b = rng.random_range(0..groups.len());
        let old_a = groups[a];
        let old_b = groups[b];
        for group in &mut groups {
            if *group == old_a || *group == old_b {
                *group = old_a.min(old_b);
            }
        }
        uf.new_buffer().stage_insert(&[
            value(a),
            value(b),
            reasons.assert(value(a), value(b)),
            v(timestamp),
        ]);
        uf.merge(&mut state);
        for (i, &group) in groups.iter().enumerate() {
            assert_eq!(uf.find(value(i)), value(group));
            if let Some(reason) = uf.canonical_reason(value(i), &mut state) {
                assert_eq!(reasons.endpoints(reason), (value(i), value(group)));
            }
        }
    }
    assert!(
        uf.parents.len() <= 100,
        "storage must not depend on the largest ID"
    );
}

#[test]
fn subscriptions_snapshots_and_clear_do_not_share_pending_writes() {
    empty_execution_state!(state);
    let mut uf = ExplainedUfTable::new(None);
    let start = uf.start_cursor();
    uf.new_buffer().stage_insert(&[v(8), v(5), v(0), v(0)]);
    assert!(uf.events_since(start).unwrap().is_empty());
    uf.merge(&mut state);
    let acknowledged = uf.cursor();
    assert_eq!(uf.events_since(start).unwrap().len(), 1);
    let mut snapshot = uf.clone();
    uf.new_buffer().stage_insert(&[v(5), v(2), v(0), v(1)]);
    snapshot.merge(&mut state);
    assert_eq!(snapshot.find(v(8)), v(5));
    uf.merge(&mut state);
    assert_eq!(uf.events_since(acknowledged).unwrap().len(), 1);
    assert_eq!(snapshot.find(v(8)), v(5));
    assert!(snapshot.events_since(uf.cursor()).is_none());

    let mut old_buffer = uf.new_buffer();
    old_buffer.stage_insert(&[v(8), v(0), v(0), v(2)]);
    uf.clear();
    drop(old_buffer);
    assert!(uf.events_since(start).is_none());
    assert!(!uf.merge(&mut state).added);
    assert_eq!(uf.find(v(8)), v(8));
}

#[test]
fn parallel_publishers_are_committed_in_timestamp_order() {
    empty_execution_state!(state);
    let mut uf = ExplainedUfTable::new(None);
    std::thread::scope(|scope| {
        for timestamp in (0..12).rev() {
            let mut buffer = uf.new_buffer();
            scope.spawn(move || {
                for i in 1..100 {
                    buffer.stage_insert(&[v(0), v(timestamp * 100 + i), v(0), v(timestamp)]);
                }
            });
        }
    });
    uf.merge(&mut state);
    assert_eq!(uf.len(), 12 * 99);
    assert!(
        uf.events
            .windows(2)
            .all(|w| w[0].timestamp <= w[1].timestamp)
    );
    let filtered = uf.refine(
        uf.all(),
        &[Constraint::GeConst {
            col: ColumnId::new(3),
            val: v(10),
        }],
    );
    assert_eq!(filtered.size(), 2 * 99);
    let mut count = 0;
    uf.scan_generic(filtered.as_ref(), |_, row| {
        assert_eq!(row[1], v(0));
        count += 1;
    });
    assert_eq!(count, 2 * 99);
    // The cached-plan compiler requires timestamp constraints to have a fast
    // pushdown, including empty ranges and values absent from the table.
    for timestamp in 0..14 {
        let col = ColumnId::new(3);
        let val = v(timestamp);
        for constraint in [
            Constraint::EqConst { col, val },
            Constraint::LtConst { col, val },
            Constraint::LeConst { col, val },
            Constraint::GtConst { col, val },
            Constraint::GeConst { col, val },
        ] {
            let fast = uf
                .fast_subset(&constraint)
                .expect("timestamp fast pushdown");
            let slow = uf.refine_one(uf.all(), &constraint);
            assert_eq!(fast.size(), slow.size());
        }
    }
}

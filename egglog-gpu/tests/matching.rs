use std::sync::Arc;

use egglog::CommandOutput;
use egglog_core_relations::{MatchBackend, MatchRelation, Value, Variable};
use egglog_gpu::{AdapterMode, Matcher};
use egglog_numeric_id::NumericId;
use rand::{Rng, SeedableRng, rngs::StdRng};

#[test]
fn shader_validates_without_an_adapter() {
    let module = naga::front::wgsl::parse_str(include_str!("../src/join.wgsl")).unwrap();
    naga::valid::Validator::new(
        naga::valid::ValidationFlags::all(),
        naga::valid::Capabilities::empty(),
    )
    .validate(&module)
    .unwrap();
}

#[test]
fn unused_body_columns_preserve_action_multiplicity() {
    use egglog_core_relations::{Database, FlatTable, PlanStrategy, make_external_func};
    use std::sync::atomic::{AtomicUsize, Ordering};
    let run = |accelerated| {
        let mut db = Database::new();
        if accelerated {
            db.set_match_backend(Some(Arc::new(Matcher::simulated(100))));
        }
        let table = db.add_table(FlatTable::new(2), [], []);
        let filter = db.add_table(FlatTable::new(1), [], []);
        {
            let mut buffer = db.new_buffer(table);
            buffer.stage_insert(&[Value::new(1), Value::new(2)]);
            buffer.stage_insert(&[Value::new(1), Value::new(3)]);
            let mut filter_buffer = db.new_buffer(filter);
            filter_buffer.stage_insert(&[Value::new(1)]);
        }
        db.merge_all();
        let count = Arc::new(AtomicUsize::new(0));
        let count_action = count.clone();
        let action = db.add_external_function(Box::new(make_external_func(move |_, _| {
            count_action.fetch_add(1, Ordering::Relaxed);
            Some(Value::new(0))
        })));
        let mut builder = db.new_rule_set();
        let mut query = builder.new_rule();
        query.set_plan_strategy(PlanStrategy::Gj);
        query.set_no_decomp(true);
        let x = query.new_var();
        let y = query.new_var();
        query.add_atom(table, &[x.into(), y.into()], []).unwrap();
        query.add_atom(filter, &[x.into()], []).unwrap();
        let mut rule = query.build();
        rule.call_external(action, &[x.into()]).unwrap();
        rule.build();
        let rules = builder.build();
        db.run_rule_set(&rules, Default::default(), None);
        count.load(Ordering::Relaxed)
    };
    assert_eq!(run(true), run(false));
}

fn canonical(mut relation: MatchRelation) -> (Vec<Variable>, Vec<Vec<Value>>) {
    let mut order: Vec<_> = (0..relation.variables.len()).collect();
    order.sort_by_key(|&i| relation.variables[i]);
    let mut rows: Vec<Vec<_>> = relation
        .rows
        .drain(..)
        .map(|r| order.iter().map(|&i| r[i]).collect())
        .collect();
    rows.sort_unstable();
    rows.dedup();
    (order.iter().map(|&i| relation.variables[i]).collect(), rows)
}

// Independent nested-loop oracle, including zero-column and empty relations.
fn naive(atoms: &[MatchRelation]) -> MatchRelation {
    let mut result = MatchRelation {
        variables: vec![],
        rows: vec![vec![]],
    };
    for atom in atoms {
        let extra: Vec<_> = atom
            .variables
            .iter()
            .enumerate()
            .filter(|(_, v)| !result.variables.contains(v))
            .map(|(i, _)| i)
            .collect();
        let mut rows = Vec::new();
        for l in &result.rows {
            for r in &atom.rows {
                if result.variables.iter().enumerate().all(|(i, v)| {
                    atom.variables
                        .iter()
                        .position(|w| w == v)
                        .is_none_or(|j| l[i] == r[j])
                }) {
                    let mut row = l.clone();
                    row.extend(extra.iter().map(|&j| r[j]));
                    rows.push(row);
                }
            }
        }
        result
            .variables
            .extend(extra.iter().map(|&j| atom.variables[j]));
        result.rows = rows;
    }
    result
}

fn random_joins(matcher: &Matcher, cases: usize) {
    let mut rng = StdRng::seed_from_u64(931);
    for case in 0..cases {
        let atoms: Vec<_> = (0..rng.random_range(0..5))
            .map(|_| {
                let variables: Vec<_> = (0..4)
                    .filter(|_| rng.random_bool(0.5))
                    .map(Variable::new)
                    .collect();
                let mut rows: Vec<Vec<_>> = (0..rng.random_range(0..12))
                    .map(|_| {
                        variables
                            .iter()
                            .map(|_| Value::new(rng.random_range(0..5)))
                            .collect()
                    })
                    .collect();
                rows.sort_unstable();
                rows.dedup();
                MatchRelation { variables, rows }
            })
            .collect();
        let expected = canonical(naive(&atoms));
        let actual = canonical(matcher.evaluate(atoms).unwrap());
        assert_eq!(actual, expected, "random query {case}");
    }
    assert_eq!(matcher.statistics().fallbacks, 0);
}

fn skewed_join(matcher: &Matcher) {
    let atoms = vec![
        MatchRelation {
            variables: vec![Variable::new(0), Variable::new(1)],
            rows: (0..131)
                .map(|i| {
                    vec![
                        Value::new(i),
                        Value::new(if i % 3 == 0 { u32::MAX - 1 } else { 0 }),
                    ]
                })
                .collect(),
        },
        MatchRelation {
            variables: vec![Variable::new(1), Variable::new(2)],
            rows: (0..257)
                .map(|i| vec![Value::new(u32::MAX - 1), Value::new(i)])
                .collect(),
        },
    ];
    assert_eq!(
        canonical(matcher.evaluate(atoms.clone()).unwrap()),
        canonical(naive(&atoms))
    );
}

#[test]
fn simulated_joins_match_independent_oracle() {
    let matcher = Matcher::simulated(1_000_000);
    random_joins(&matcher, 1000);
    skewed_join(&matcher);
}

fn run(source: &str, matcher: Option<Arc<Matcher>>) -> String {
    let mut graph = egglog_experimental::new_experimental_egraph_with_term_encoding();
    if let Some(matcher) = matcher {
        graph.set_match_backend(Some(matcher));
    }
    let outputs = graph.parse_and_run_program(None, source).unwrap();
    CommandOutput::snapshot_stable_under_proof_encoding(&outputs)
}

fn programs(matcher: Arc<Matcher>) {
    for source in [
        include_str!("../examples/scheduled-terms.egg"),
        include_str!("../../egglog/tests/term-encoding-subsume-rebuild-bug.egg"),
        include_str!("../../egglog/tests/repro-small-rebuild-fail-term-encoding.egg"),
        include_str!("../../egglog/tests/repro-typecheck-term-encoding.egg"),
        include_str!("../../egglog/tests/custom-eqsort-output-rebuild.egg"),
        include_str!("../../egglog/tests/merge-during-rebuild.egg"),
        include_str!("../../egglog/tests/merge-saturates.egg"),
        include_str!("../../egglog/tests/subsume-relation.egg"),
        r#"
            (datatype T (N i64) (F T))
            (relation seed (i64))
            (seed 1) (seed 2)
            (ruleset a) (ruleset b)
            (rule ((seed x)) ((F (N 0))) :ruleset a)
            (rule ((seed x)) ((F (N 0))) :ruleset b)
            (run-schedule (repeat 3 (seq (run a) (run b))))
            (print-size N) (print-size F)
            (push)
            (union (N 0) (N 1))
            (run 1)
            (check (= (F (N 0)) (F (N 1))))
            (pop)
            (fail (check (= (N 0) (N 1))))
            (run-schedule (run a))
            (print-size N) (print-size F)
        "#,
        r#"
            (relation edge (i64 i64))
            (relation path (i64 i64))
            (edge 1 2) (edge 2 3) (edge 3 4)
            (ruleset step)
            (rule ((edge x y)) ((path x y)) :ruleset step)
            (rule ((path x y) (path y z)) ((path x z)) :ruleset step)
            (run-schedule (run step))
            (fail (check (path 1 3)))
            (run-schedule (run step :until (path 1 3)))
            (check (path 1 3))
            (fail (check (path 1 4)))
            (run-schedule (saturate step))
            (check (path 1 4))
            (print-size path)
        "#,
    ] {
        assert_eq!(run(source, Some(matcher.clone())), run(source, None));
    }
    assert!(matcher.statistics().plans > 0);
    assert!(matcher.statistics().joins > 0);
}

#[test]
fn simulated_term_programs_match_native() {
    let matcher = Arc::new(Matcher::simulated(1_000_000));
    programs(matcher.clone());
    assert_eq!(matcher.statistics().fallbacks, 0);
}

#[test]
fn bounded_fallback_preserves_program_results() {
    let matcher = Arc::new(Matcher::simulated(1));
    let source = include_str!("../examples/scheduled-terms.egg");
    assert_eq!(run(source, Some(matcher.clone())), run(source, None));
    assert!(matcher.statistics().fallbacks > 0);
}

#[test]
fn unsupported_sources_have_native_errors() {
    let error = |source, accelerated| {
        let mut graph = egglog_experimental::new_experimental_egraph_with_term_encoding();
        if accelerated {
            graph.set_match_backend(Some(Arc::new(Matcher::simulated(1_000_000))));
        }
        let error = graph.parse_and_run_program(None, source).unwrap_err();
        assert!(matches!(
            error,
            egglog::Error::UnsupportedProofCommand { .. }
        ));
        error.to_string()
    };
    for source in [
        include_str!("../../egglog/tests/merge-action-block.egg"),
        include_str!("../../egglog/tests/merge_read.egg"),
        include_str!("../../egglog/tests/unsafe-seminaive-read-prim.egg"),
    ] {
        let native = error(source, false);
        assert_eq!(error(source, true), native);
    }
}

#[test]
#[ignore = "requires a Vulkan software adapter; run explicitly with --ignored"]
fn software_vulkan_matches_oracle_and_native_egglog() {
    let matcher = Arc::new(Matcher::vulkan(AdapterMode::Software, 1_000_000).unwrap());
    eprintln!("{}", matcher.adapter());
    random_joins(&matcher, 200);
    skewed_join(&matcher);
    programs(matcher.clone());
    assert_eq!(matcher.statistics().fallbacks, 0);
}

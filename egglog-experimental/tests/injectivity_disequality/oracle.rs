//! An iterative finite-model oracle, independent of the query's goal search.

use std::collections::HashSet;
use std::fmt::Write;

use egglog_experimental::{DisequalityEncoding, new_experimental_egraph_with_options};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Argument {
    Class(usize),
    Native(i64),
}

struct Application {
    constructor: &'static str,
    arguments: Vec<Argument>,
    result: usize,
    injective: bool,
}

/// Close facts by repeatedly applying the two laws to every application pair.
/// Classes are a fixed, already committed partition; this oracle never runs
/// equality cancellation, and deliberately does not mirror the query's BFS.
fn finite_closure(
    applications: &[Application],
    assertions: &[(usize, usize)],
) -> HashSet<(usize, usize)> {
    let mut known: HashSet<_> = assertions
        .iter()
        .map(|&(a, b)| (a.min(b), a.max(b)))
        .collect();
    loop {
        let before = known.len();
        for a in applications {
            for b in applications {
                if a.constructor != b.constructor {
                    continue;
                }
                let results = (a.result.min(b.result), a.result.max(b.result));
                if a.injective
                    && a.arguments
                        .iter()
                        .zip(&b.arguments)
                        .any(|(a, b)| match (*a, *b) {
                            (Argument::Class(a), Argument::Class(b)) => {
                                known.contains(&(a.min(b), a.max(b)))
                            }
                            (Argument::Native(a), Argument::Native(b)) => a != b,
                            _ => panic!("application schemas disagree"),
                        })
                {
                    known.insert(results);
                }
                if known.contains(&results) {
                    for (focus, (left, right)) in a.arguments.iter().zip(&b.arguments).enumerate() {
                        if let (Argument::Class(left), Argument::Class(right)) = (*left, *right)
                            && a.arguments
                                .iter()
                                .zip(&b.arguments)
                                .enumerate()
                                .all(|(position, (a, b))| position == focus || a == b)
                        {
                            known.insert((left.min(right), left.max(right)));
                        }
                    }
                }
            }
        }
        if known.len() == before {
            return known;
        }
    }
}

#[test]
fn every_pair_matches_the_finite_fragment_least_fixed_point() {
    use Argument::{Class, Native};

    let base = [
        ("Plain", vec![Class(0), Class(4)], 5, false),
        ("Plain", vec![Class(1), Class(4)], 6, false),
        ("Triple", vec![Class(0), Class(4), Class(3)], 7, false),
        ("Triple", vec![Class(1), Class(4), Class(3)], 8, false),
        ("Marked", vec![Class(0), Class(2)], 9, true),
        ("Marked", vec![Class(1), Class(2)], 10, true),
        ("Unary", vec![Class(9)], 11, false),
        ("Unary", vec![Class(10)], 12, false),
        ("Mixed", vec![Native(0), Class(2)], 13, false),
        ("Mixed", vec![Native(1), Class(3)], 14, false),
        ("Plain", vec![Class(2), Class(2)], 15, false),
        ("Plain", vec![Class(3), Class(3)], 16, false),
        ("Native", vec![Native(0), Class(2)], 17, true),
        ("Native", vec![Native(1), Class(2)], 18, true),
        ("Native", vec![Native(0), Class(3)], 19, true),
        ("Plain", vec![Class(17), Class(4)], 20, false),
        ("Plain", vec![Class(18), Class(4)], 21, false),
    ];
    let seeds = [
        (0, 1),
        (5, 6),
        (7, 8),
        (11, 12),
        (13, 14),
        (15, 16),
        (17, 19),
    ];
    let masks = [0, 1, 2, 4, 8, 16, 32, 64, 3, 12, 48, 65, 85, 42, 126, 127];
    let mut graphs = 0;
    let mut queries = 0;
    let mut positive = 0;
    let mut negative = 0;
    for cyclic in [false, true] {
        let mut canonical: Vec<_> = (0..22).collect();
        if cyclic {
            canonical[5] = 0;
            canonical[6] = 1;
        }
        let applications: Vec<_> = base
            .iter()
            .map(|(constructor, arguments, result, injective)| Application {
                constructor,
                arguments: arguments
                    .iter()
                    .map(|argument| match *argument {
                        Class(class) => Class(canonical[class]),
                        Native(value) => Native(value),
                    })
                    .collect(),
                result: canonical[*result],
                injective: *injective,
            })
            .collect();
        for mask in masks {
            let assertions: Vec<_> = seeds
                .iter()
                .enumerate()
                .filter(|(index, _)| mask & (1 << index) != 0)
                .map(|(_, &(a, b))| (canonical[a], canonical[b]))
                .collect();
            let expected = finite_closure(&applications, &assertions);
            let mut setup = String::from(
                "(datatype Node (Atom i64) (Plain Node Node) (Triple Node Node Node)\n\
                 (Marked Node Node :injective) (Unary Node) (Mixed i64 Node)\n\
                 (Native i64 Node :injective))\n",
            );
            for class in 0..22 {
                writeln!(setup, "(let v{class} (Atom {class}))").unwrap();
            }
            for (constructor, arguments, result, _) in &base {
                write!(setup, "(union v{result} ({constructor}").unwrap();
                for argument in arguments {
                    match argument {
                        Class(class) => write!(setup, " v{class}").unwrap(),
                        Native(value) => write!(setup, " {value}").unwrap(),
                    }
                }
                setup.push_str("))\n");
            }
            if cyclic {
                setup.push_str("(union v0 v5) (union v1 v6)\n");
            }
            for &(a, b) in &assertions {
                writeln!(setup, "(disequal v{a} v{b})").unwrap();
            }
            let mut checks = String::new();
            for a in 0..22 {
                for b in a..22 {
                    let (left, right) = (canonical[a], canonical[b]);
                    let known = expected.contains(&(left.min(right), left.max(right)));
                    if known {
                        writeln!(checks, "(check (known-disequal? v{a} v{b}))").unwrap();
                        positive += 2;
                    } else {
                        writeln!(checks, "(fail (check (known-disequal? v{a} v{b})))").unwrap();
                        negative += 2;
                    }
                }
            }
            for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
                let mut graph = new_experimental_egraph_with_options(false, encoding);
                graph.parse_and_run_program(None, &setup).unwrap();
                let rows = graph.num_tuples();
                let tables = graph.get_function_names();
                graph
                    .parse_and_run_program(None, &checks)
                    .unwrap_or_else(|error| {
                        panic!("{encoding:?}, cyclic={cyclic}, mask={mask}: {error}")
                    });
                assert_eq!(graph.num_tuples(), rows);
                assert_eq!(graph.get_function_names(), tables);
                graphs += 1;
                queries += 253;
            }
        }
    }
    assert_eq!(graphs, 64);
    assert_eq!(queries, 16_192);
    assert!(positive > 0 && negative > 0);
    eprintln!(
        "finite oracle: {graphs} graphs, {queries} pairs, {positive} positive, {negative} unknown"
    );
}

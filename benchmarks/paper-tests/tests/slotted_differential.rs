//! Compare slotted encodings with live native-reference executions on small cases.
//!
//! Each .egg contains a source program. Its .ref JSON contains the corresponding
//! native program for multi-pattern matching and, optionally, nested matching.
//! Compare each encoding with its matching native policy using snapshot
//! substitution. Agreement cases require equal probe partitions and logical
//! e-class/e-node counts. Export validation also checks renamings and edge domains.
//! Curated expectations pin a known divergence and guard, aliasing or count
//! properties. These are assertions alongside inputs; no graph isomorphism is run.
use egglog::{EGraph, Error};
use egglog_experimental::slotted::{Compiler, Options, export, new_egraph};
use serde::Deserialize;
use slotted_reference::{Substitution, run_spec};
use std::{collections::BTreeMap, path::Path};

/// Additional assertions for selected cases. With an empty expectation block,
/// live native/encoded partition and count equality are still required.
#[derive(Deserialize, Default)]
#[serde(deny_unknown_fields)]
struct Expect {
    /// Optional prescribed encoding partition; groups contain zero-based probe indices.
    encoding_partition: Option<String>,
    /// Prescribed native partition when recording a known limitation.
    reference_partition: Option<String>,
    /// Reason for a known divergence. Require both prescribed partitions and
    /// require them to differ; a changed or unexpectedly fixed limitation fails.
    limitation: Option<String>,
    /// Guarded array-case name whose probe partition must differ from this
    /// guard-stripped case, so a guard cannot pass the test vacuously.
    differs_from: Option<String>,
    /// Across encodings: true requires more nodes with aliasing than without
    /// aliasing; false requires equal counts. Native policy comparisons remain separate.
    full_nodes_exceed_compat: Option<bool>,
    /// Exact [e-class count, e-node count] for the encoded run, beyond live agreement.
    expected_counts: Option<[usize; 2]>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    /// Executable native-reference program for the aliasing-capable encoding.
    multi: String,
    /// Optional native-reference program for the no-aliasing encoding.
    nested: Option<String>,
    /// Source terms whose equality partition is observed after the workload.
    probes: Vec<String>,
    expect: Expect,
}

/// Observe class identity through the public query language. Renaming equality
/// groups readings of one class even when their slot maps differ.
fn partition(graph: &mut EGraph, compiler: &mut Compiler, probes: &[String]) -> String {
    let mut groups: Vec<Vec<usize>> = Vec::new();
    for (i, probe) in probes.iter().enumerate() {
        let group = groups.iter().position(|group| {
            let source = format!("(check (renaming-= {probe} {}))", probes[group[0]]);
            let lowered = compiler.compile(None, &source).unwrap();
            match graph.parse_and_run_program(None, &lowered) {
                Ok(_) => true,
                Err(Error::CheckError(..)) => false,
                Err(error) => panic!("invalid partition query: {error}"),
            }
        });
        if let Some(group) = group {
            groups[group].push(i);
        } else {
            groups.push(vec![i]);
        }
    }
    let mut rendered: Vec<_> = groups
        .iter()
        .map(|group| {
            format!(
                "[{}]",
                group
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            )
        })
        .collect();
    rendered.sort();
    format!("{} missing[[]]", rendered.join(""))
}

#[test]
fn frozen_semantic_pairs_have_reference_partitions_and_validated_counts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let directory = root.join("benchmarks/slotted/correctness");
    let mut families = BTreeMap::<String, usize>::new();
    let mut partitions = BTreeMap::new();
    let mut guards = Vec::new();
    for path in glob::glob(directory.join("**/*.egg").to_str().unwrap()).unwrap() {
        let path = path.unwrap();
        let name = path.strip_prefix(&directory).unwrap().display().to_string();
        eprintln!("Checking {name}");
        *families
            .entry(
                path.parent()
                    .unwrap()
                    .file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_owned(),
            )
            .or_default() += 1;
        let fixture: Fixture =
            serde_json::from_str(&std::fs::read_to_string(path.with_extension("ref")).unwrap())
                .unwrap();
        let source = std::fs::read_to_string(&path).unwrap();
        let mut sizes = Vec::new();
        for (nested, spec) in [
            (false, Some(&fixture.multi)),
            (true, fixture.nested.as_ref()),
        ] {
            let Some(spec) = spec else {
                continue;
            };
            let mut compiler = Compiler::new(Options {
                no_aliasing: nested,
                ..Default::default()
            });
            let mut graph = new_egraph();
            graph.set_num_threads(1);
            let lowered = compiler
                .compile(Some(path.display().to_string()), &source)
                .unwrap();
            graph
                .parse_and_run_program(None, &lowered)
                .unwrap_or_else(|error| panic!("{name}: {error}"));
            // This validates raw renamings, complete groups and edge domains;
            // no isomorphism comparison or witness search is requested.
            let exported = export::export(&graph).unwrap_or_else(|error| panic!("{name}: {error}"));
            let counts = (exported.counts.classes, exported.counts.nodes);
            drop(exported);
            let native = run_spec(
                spec,
                Substitution::Snapshot,
                slotted_reference::ProofMode::Off,
            )
            .unwrap_or_else(|error| panic!("{name}: {error}"));
            assert!(
                native.goals.iter().all(|&goal| goal),
                "{name}: reference target failed"
            );
            let observed = partition(&mut graph, &mut compiler, &fixture.probes);
            let after = export::counts(&graph).unwrap();
            assert_eq!(
                counts,
                (after.classes, after.nodes),
                "{name}: observing probes changed the graph"
            );
            if fixture.expect.limitation.is_some() {
                assert_eq!(
                    Some(&observed),
                    fixture.expect.encoding_partition.as_ref(),
                    "{name}: recorded limitation changed"
                );
                assert_eq!(
                    Some(&native.partition),
                    fixture.expect.reference_partition.as_ref(),
                    "{name}: reference limitation changed"
                );
                assert_ne!(
                    observed, native.partition,
                    "{name}: stale known limitation; move to agreement coverage"
                );
            } else {
                assert_eq!(
                    observed, native.partition,
                    "{name}: class partitions differ"
                );
                assert_eq!(
                    counts,
                    (native.classes, native.nodes),
                    "{name}: logical counts differ"
                );
                if let Some(expected) = &fixture.expect.encoding_partition {
                    assert_eq!(&observed, expected, "{name}: prescribed partition changed");
                }
            }
            if let Some([classes, nodes]) = fixture.expect.expected_counts {
                assert_eq!(counts, (classes, nodes), "{name}: expected counts changed");
            }
            if !nested {
                partitions.insert(name.clone(), observed);
            }
            sizes.push(counts.1);
        }
        if let Some(differs) = fixture.expect.full_nodes_exceed_compat {
            assert_eq!(
                sizes.len(),
                2,
                "{name}: missing compatibility representation"
            );
            if differs {
                assert!(sizes[0] > sizes[1], "{name}: aliasing difference lost");
            } else {
                assert_eq!(sizes[0], sizes[1], "{name}: unexpected aliasing difference");
            }
        }
        if let Some(peer) = fixture.expect.differs_from {
            guards.push((name, format!("array/{peer}.egg")));
        }
    }
    for (unguarded, guarded) in guards {
        assert_ne!(
            partitions[&unguarded], partitions[&guarded],
            "guard is vacuous: {guarded}"
        );
    }
    assert_eq!(
        families,
        BTreeMap::from([
            ("toy".into(), 59),
            ("array".into(), 20),
            ("sdql".into(), 28),
            ("nested".into(), 12),
            ("eval".into(), 3),
        ]),
        "frozen semantic coverage changed"
    );
}

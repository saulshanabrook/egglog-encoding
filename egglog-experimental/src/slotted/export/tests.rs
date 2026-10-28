use super::*;
use crate::slotted::{Compiler, Options, new_egraph};
use egglog::Read;

fn snapshot(graph: &EGraph) -> Snapshot {
    let layouts = Layouts::load(graph).unwrap();
    Snapshot::read(
        graph,
        &layouts.carriers[0],
        &layouts.constructors,
        &BTreeMap::new(),
    )
    .unwrap()
}

fn document(snapshot: &Snapshot) -> Result<AnnotatedEGraph, String> {
    let mut out = AnnotatedEGraph {
        slotted: Some(Slotted::default()),
        ..Default::default()
    };
    snapshot.append(&mut out, "U", true)?;
    Graph::try_from(&out).map_err(|e| e.to_string())?;
    Ok(out)
}

fn run(source: &str) -> EGraph {
    let mut graph = new_egraph();
    let program = Compiler::new(Options::default())
        .compile(None, source)
        .unwrap();
    graph.parse_and_run_program(None, &program).unwrap();
    graph
}

#[test]
fn native_export_preserves_rows_types_and_binders() {
    let graph = run(
        "(sort U) (constructor F (U U) U) (constructor Lam (U U) U :binder 0) (let a (Lam $x (F $x $y))) (run 0)",
    );
    let exported = export(&graph).unwrap();
    assert_eq!((exported.counts.classes, exported.counts.nodes), (3, 3));
    assert_eq!(exported.graph.egraph.nodes.len(), 3);
    assert!(
        exported
            .graph
            .egraph
            .class_data
            .values()
            .all(|c| c.typ.as_deref() == Some("U"))
    );
    let (id, node) = exported
        .graph
        .egraph
        .nodes
        .iter()
        .find(|(_, n)| n.op == "Lam")
        .unwrap();
    assert_eq!(node.children.len(), 1);
    assert!(matches!(
        exported.graph.slotted.as_ref().unwrap().nodes[id].arguments[0],
        Argument::Slot { .. }
    ));
}

#[test]
fn export_checks_actual_groups_and_does_not_run_maintenance() {
    let mut graph = run(
        "(sort U) (constructor F (U U) U) (let a (F $0 $1)) (union (F $0 $1) (F $1 $0)) (run 0)",
    );
    let good = export(&graph).unwrap();
    assert_eq!(
        good.graph
            .slotted
            .as_ref()
            .unwrap()
            .classes
            .values()
            .map(|c| c.group.len())
            .max(),
        Some(2)
    );
    graph
        .parse_and_run_program(None, "(delete (FreeVars_0 (SlottedVar_0 0)))")
        .unwrap();
    assert!(export(&graph).unwrap_err().contains("FreeVars"));
}

#[test]
fn export_supports_multiple_carriers_and_escaped_payloads() {
    let graph = run(
        "(sort A) (sort B) (constructor Num (i64) A) (constructor Text (String) B) (let a (Num 1)) (let b (Text \"a\\\"b\")) (run 0)",
    );
    let exported = export(&graph).unwrap();
    assert_eq!(exported.counts.nodes, 4);
    assert_eq!(exported.counts.classes, 4);
    assert!(
        exported
            .graph
            .egraph
            .nodes
            .values()
            .any(|n| n.op == "(Text \"a\\\"b\")")
    );
}

#[test]
fn export_requires_one_variable_for_every_carrier() {
    let mut graph = run("(datatype* (Expr) (Value (Num i64))) (let n (Num 7)) (run 0)");
    let exported = export(&graph).unwrap();
    assert_eq!((exported.counts.classes, exported.counts.nodes), (3, 3));
    assert_eq!(graph.get_size("SlottedVar_0"), 1);
    assert_eq!(graph.get_size("SlottedVar_1"), 1);
    graph
        .parse_and_run_program(None, "(delete (SlottedVar_1 0))")
        .unwrap();
    assert!(
        export(&graph)
            .unwrap_err()
            .contains("expected one raw variable row")
    );
}

#[test]
fn export_preserves_sort_names() {
    let graph = run(r"(datatype Expr\Name (F Expr\Name)) (let a (F $x)) (run 0)");
    let exported = export(&graph).unwrap();
    assert_eq!(exported.counts.nodes, 2);
    assert!(
        exported
            .graph
            .egraph
            .class_data
            .values()
            .all(|c| c.typ.as_deref() == Some(r"Expr\Name"))
    );
}

#[test]
fn raw_edges_are_checked_before_projection() {
    let graph = run(
        "(sort U) (constructor Null () U) (constructor F (U U) U) (constructor Lam (U U) U :binder 0) (let a (Lam $a (F $a (Null)))) (run 0)",
    );
    let original = snapshot(&graph);
    document(&original).unwrap();
    let binder = original.rows.iter().position(|r| r.label == "Lam").unwrap();
    let null = original
        .rows
        .iter()
        .find(|r| r.label == "Null")
        .unwrap()
        .class;
    let mut mutants = Vec::new();
    let mut bad = original.clone();
    bad.rows[binder].edges[0].map.insert(17, 18);
    mutants.push(("extra binder domain", bad));
    let mut bad = original.clone();
    bad.rows[binder].edges[0].class = null;
    mutants.push(("wrong binder class", bad));
    let mut bad = original.clone();
    bad.rows.iter_mut().find(|r| r.label == "F").unwrap().edges[1]
        .map
        .insert(0, 19);
    mutants.push(("extra ordinary edge domain", bad));
    let mut bad = original.clone();
    bad.rows[binder].edges[1].map.clear();
    mutants.push(("missing ordinary edge domain", bad));
    let mut bad = original.clone();
    bad.rows.iter_mut().find(|r| r.label == "F").unwrap().edges[0]
        .map
        .insert(0, 20);
    mutants.push(("class slots absent from node", bad));
    let mut bad = original.clone();
    bad.slots.remove(&null);
    mutants.push(("missing FreeVars", bad));
    for (name, bad) in mutants {
        assert!(document(&bad).is_err(), "accepted {name}");
    }
}

#[test]
fn native_reads_reject_invalid_variables_renamings_and_metadata() {
    let source =
        "(sort U) (constructor Null () U) (constructor F (U U) U) (let a (F $0 (Null))) (run 0)";
    for mutation in [
        "(SlottedVar_0 1)",
        "(F (map-of 0 2 1 2) (SlottedVar_0 0) (map-empty) (Null))",
        "(delete (SlottedEdgeLayout \"F\" 0))",
        "(delete (SlottedNodeLayout \"Null\" 0))",
        "(set (SlottedNodeLayout \"F\" 99) ())",
        "(set (SlottedEdgeLayout \"F\" 1) ())",
    ] {
        let mut graph = run(source);
        graph.parse_and_run_program(None, mutation).unwrap();
        assert!(export(&graph).is_err(), "accepted {mutation}");
    }
    // An identity map and a nonidentity FreeVars map can share the same keys;
    // replace the row instead of invoking its intersection merge.
    let mut graph = run(source);
    graph.parse_and_run_program(None, "(delete (FreeVars_0 (SlottedVar_0 0))) (set (FreeVars_0 (SlottedVar_0 0)) (map-of 0 1))").unwrap();
    assert!(export(&graph).unwrap_err().contains("identity"));
}

#[test]
fn partial_and_inconsistent_leader_frames_are_rejected() {
    let graph = run("(sort U) (constructor F (U U) U) (let a (F $1 $2)) (let b (F $3 $4)) (run 0)");
    let original = snapshot(&graph);
    document(&original).unwrap();
    let link = original
        .links
        .iter()
        .position(|l| l.source != l.target && l.map.len() == 2)
        .unwrap();
    for reverse in [false, true] {
        let mut bad = original.clone();
        let l = &mut bad.links[link];
        if reverse {
            std::mem::swap(&mut l.source, &mut l.target);
            l.map = inverse(&l.map);
        }
        l.map.pop_first();
        assert!(document(&bad).unwrap_err().contains("bijection"));
        let mut bad = original.clone();
        let l = &mut bad.links[link];
        let image = *l.map.values().next().unwrap();
        for value in l.map.values_mut() {
            *value = image;
        }
        if reverse {
            std::mem::swap(&mut l.source, &mut l.target);
            l.map = inverse(&l.map);
        }
        assert!(
            document(&bad).is_err(),
            "accepted a non-injective leader frame"
        );
    }
    let mut bad = original.clone();
    let mut alternative = bad.links[link].clone();
    let images: Vec<_> = alternative.map.values().copied().collect();
    for (value, replacement) in alternative.map.values_mut().zip(images.into_iter().rev()) {
        *value = replacement;
    }
    bad.links.push(alternative);
    assert!(document(&bad).unwrap_err().contains("inconsistent"));
}

#[test]
fn groups_are_complete_recorded_values_not_repaired_from_leader_links() {
    let graph = run(
        "(sort U) (constructor G (U U) U) (let a (G (G $0 $1) $2)) (union (G (G $0 $1) $2) (G (G $1 $2) $0)) (run 0)",
    );
    let original = snapshot(&graph);
    document(&original).unwrap();
    let class = *original
        .groups
        .iter()
        .find(|(_, g)| g.len() == 3)
        .unwrap()
        .0;
    for keep in [0, 1, 2] {
        let mut bad = original.clone();
        bad.groups.get_mut(&class).unwrap().truncate(keep);
        if keep == 1 {
            // A proper subgroup is valid input to the generic checker, but the
            // export must still agree with the recorded nonidentity leader links.
            bad.links.push(Link {
                source: class,
                target: class,
                map: original.groups[&class][1].clone(),
            });
        }
        assert!(document(&bad).is_err(), "accepted {keep} elements of C3");
    }
    let mut bad = original.clone();
    bad.groups
        .get_mut(&class)
        .unwrap()
        .retain(|p| p.iter().any(|(a, b)| a != b));
    assert!(document(&bad).is_err());
}

#[test]
fn export_preserves_unretired_rows_and_empty_classes() {
    let graph = run(
        "(sort U) (constructor Null () U) (constructor F (U U) U) (let a (F $1 (Null))) (let b (F $2 (Null))) (run 0)",
    );
    let mut snapshot = snapshot(&graph);
    let before = document(&snapshot).unwrap();
    let mut extra = snapshot
        .rows
        .iter()
        .find(|r| r.label == "F")
        .unwrap()
        .clone();
    let link = snapshot
        .links
        .iter()
        .find(|l| l.source != l.target && l.target == extra.class)
        .unwrap();
    extra.class = link.source;
    for edge in &mut extra.edges {
        edge.map = compose(&link.map, &edge.map);
    }
    snapshot.rows.push(extra);
    let after = document(&snapshot).unwrap();
    assert_eq!(after.egraph.nodes.len(), before.egraph.nodes.len() + 1);
    let left = Graph::try_from(&before).unwrap();
    let right = Graph::try_from(&after).unwrap();
    assert!(matches!(
        egraph_isomorphism::find_isomorphism(&left, &right, Default::default()).unwrap(),
        egraph_isomorphism::Outcome::Different { .. }
    ));
    // An isolated class whose final constructor was deleted must stay visible.
    snapshot.rows.retain(|r| r.label != "F");
    let after = document(&snapshot).unwrap();
    assert_eq!(
        after.slotted.unwrap().classes.len(),
        before.slotted.unwrap().classes.len()
    );
}

#[test]
fn frame_traversal_handles_both_directions_and_out_of_order_links() {
    let graph = run(
        "(sort U) (constructor Seed (i64) U) (let a (Seed 1)) (let b (Seed 2)) (let c (Seed 3)) (run 0)",
    );
    let values = graph.read(|s| {
        (1..=3i64)
            .map(|i| s.eclass_of("Seed", (i,)).unwrap().unwrap())
            .collect::<Vec<_>>()
    });
    let variable = snapshot(&graph).variable;
    for reverse in [false, true] {
        let mut snapshot = snapshot(&graph);
        snapshot.rows.retain(|r| r.variable);
        snapshot.slots = [
            (variable, Map::from([(0, 0)])),
            (values[0], Map::from([(7, 7)])),
            (values[1], Map::from([(11, 11)])),
            (values[2], Map::from([(13, 13)])),
        ]
        .into();
        snapshot.groups = [(variable, vec![Map::from([(0, 0)])])].into();
        snapshot.links = [
            (values[1], 11, values[2], 13),
            (values[2], 13, variable, 0),
            (values[0], 7, values[1], 11),
        ]
        .into_iter()
        .map(|(a, sa, b, sb)| {
            if reverse {
                Link {
                    source: b,
                    target: a,
                    map: [(sa, sb)].into(),
                }
            } else {
                Link {
                    source: a,
                    target: b,
                    map: [(sb, sa)].into(),
                }
            }
        })
        .collect();
        let doc = document(&snapshot).unwrap();
        assert_eq!(Graph::try_from(&doc).unwrap().counts(), (1, 1));
    }
}

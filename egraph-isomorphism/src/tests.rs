use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use super::*;

fn document(value: Value) -> AnnotatedEGraph {
    serde_json::from_value(value).unwrap()
}
fn graph(value: Value) -> Graph {
    Graph::try_from(&document(value)).unwrap()
}
fn iso(a: &Graph, b: &Graph) -> Witness {
    let Outcome::Isomorphic { witness } = find_isomorphism(a, b, Limits::default()).unwrap() else {
        panic!("expected isomorphism");
    };
    verify(a, b, &witness).unwrap();
    witness
}
fn different(a: &Graph, b: &Graph) {
    assert!(matches!(
        find_isomorphism(a, b, Limits::default()).unwrap(),
        Outcome::Different { .. }
    ));
}

fn ordinary() -> Value {
    json!({"nodes": {
        "a": {"op": "a", "eclass": "A", "children": []},
        "b": {"op": "b", "eclass": "B", "children": []},
        "p": {"op": "pair", "eclass": "P", "children": ["a", "b"]}
    }, "root_eclasses": ["P"]})
}

#[test]
fn ordinary_ids_and_chosen_child_representatives_are_irrelevant() {
    let a = graph(json!({"nodes": {
        "one": {"op":"one", "eclass":"A"}, "two": {"op":"two", "eclass":"A"},
        "use": {"op":"use", "eclass":"P", "children":["one"]}
    }}));
    let b = graph(json!({"nodes": {
        "x": {"op":"two", "eclass":"Z"}, "y": {"op":"one", "eclass":"Z"},
        "z": {"op":"use", "eclass":"Q", "children":["x"]}
    }}));
    iso(&a, &b);
    let mut cost = ordinary();
    cost["nodes"]["a"]["cost"] = json!(42.0);
    iso(&graph(ordinary()), &graph(cost));
}

#[test]
fn labels_order_types_roots_and_subsumption_are_observable() {
    let a = graph(ordinary());
    let mut mutants = Vec::new();
    let mut m = ordinary();
    m["nodes"]["p"]["children"] = json!(["b", "a"]);
    mutants.push(m);
    let mut m = ordinary();
    m["nodes"]["a"]["op"] = json!("different");
    mutants.push(m);
    let mut m = ordinary();
    m["class_data"] = json!({"A":{"type":"Integer"}});
    mutants.push(m);
    let mut m = ordinary();
    m["root_eclasses"] = json!(["A"]);
    mutants.push(m);
    let mut m = ordinary();
    m["nodes"]["a"]["subsumed"] = json!(true);
    mutants.push(m);
    for m in mutants {
        different(&a, &graph(m));
    }
    let mut m = ordinary();
    m["root_eclasses"] = json!(["A", "B"]);
    let mut n = m.clone();
    n["root_eclasses"] = json!(["B", "A"]);
    different(&graph(m), &graph(n));
}

#[test]
fn duplicate_nodes_and_empty_classes_are_preserved() {
    let a = ordinary();
    let mut b = a.clone();
    b["nodes"]["duplicate"] = b["nodes"]["a"].clone();
    different(&graph(a.clone()), &graph(b));
    let mut b = a.clone();
    b["class_data"] = json!({"empty":{}});
    different(&graph(a), &graph(b.clone()));
    iso(&graph(b.clone()), &graph(b));
}

#[test]
fn cyclic_graphs_need_a_global_bijection() {
    let a = graph(json!({"nodes": {
        "a":{"op":"step","eclass":"A","children":["b"]},
        "b":{"op":"step","eclass":"B","children":["a"]}
    }}));
    let b = graph(json!({"nodes": {
        "x":{"op":"step","eclass":"X","children":["y"]},
        "y":{"op":"step","eclass":"Y","children":["x"]}
    }}));
    let c = graph(json!({"nodes": {
        "x":{"op":"step","eclass":"X","children":["x"]},
        "y":{"op":"step","eclass":"Y","children":["y"]}
    }}));
    iso(&a, &b);
    different(&a, &c);
}

fn cyclic_slots(second: [&str; 3]) -> Value {
    let renaming = |values: [&str; 3]| {
        json!({"kind":"child", "renaming": [
            ["a",values[0]], ["b",values[1]], ["c",values[2]]
        ]})
    };
    json!({
        "nodes": {
            "c":{"op":"triple","eclass":"C","children":[]},
            "p":{"op":"pair","eclass":"P","children":["c","c"]}
        },
        "slotted": {
            "classes": {
                "C":{"slots":["a","b","c"],"group":[[0,1,2],[1,2,0],[2,0,1]]},
                "P":{"slots":["x","y","z"],"group":[[0,1,2]]}
            },
            "nodes": {
                "c":{"arguments":[{"kind":"slot","slot":"a"},{"kind":"slot","slot":"b"},{"kind":"slot","slot":"c"}]},
                "p":{"arguments":[{"kind":"slot","slot":"x"},{"kind":"slot","slot":"y"},{"kind":"slot","slot":"z"},renaming(["x","y","z"]),renaming(second)]}
            }
        }
    })
}

#[test]
fn child_symmetries_are_per_occurrence_and_must_be_group_members() {
    let a = graph(cyclic_slots(["x", "y", "z"]));
    let b = graph(cyclic_slots(["y", "z", "x"]));
    let witness = iso(&a, &b);
    assert!(
        witness.classes[&"P".into()].nodes[&"p".into()]
            .children
            .iter()
            .any(|&p| p != 0)
    );
    different(&a, &graph(cyclic_slots(["x", "z", "y"])));
    let mut lost = cyclic_slots(["x", "y", "z"]);
    lost["slotted"]["classes"]["C"]["group"] = json!([[0, 1, 2]]);
    different(&a, &graph(lost));
}

fn private_slots(first: [&str; 2], second: &str) -> Value {
    json!({"nodes":{
        "a":{"op":"bind","eclass":"A"}, "b":{"op":"other","eclass":"A"}
    },"slotted":{
        "classes":{"A":{"slots":[],"group":[[]]}},
        "nodes":{
            "a":{"arguments":[{"kind":"slot","slot":first[0]},{"kind":"slot","slot":first[1]}]},
            "b":{"arguments":[{"kind":"slot","slot":second}]}
        }
    }})
}

#[test]
fn private_names_are_local_to_nodes_but_sharing_within_a_node_matters() {
    let a = graph(private_slots(["x", "x"], "x"));
    let b = graph(private_slots(["y", "y"], "z"));
    iso(&a, &b);
    different(&a, &graph(private_slots(["y", "z"], "z")));
}

#[test]
fn malformed_annotations_are_rejected_without_repair() {
    let mut mutants = Vec::new();
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["classes"]["C"]["group"] = json!([[0, 1, 2], [1, 2, 0]]);
    mutants.push(m);
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["classes"]["C"]["group"] = json!([[1, 2, 0], [2, 0, 1]]);
    mutants.push(m);
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["classes"]["C"]["group"] = json!([[0, 0, 2]]);
    mutants.push(m);
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["classes"]["C"]["group"] = json!([[0, 1, 2], [0, 1, 2]]);
    mutants.push(m);
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["classes"]["C"]["slots"] = json!(["a", "a", "c"]);
    mutants.push(m);
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["nodes"].as_object_mut().unwrap().remove("c");
    mutants.push(m);
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["nodes"]["p"]["arguments"][3]["renaming"] =
        json!([["a", "x"], ["b", "x"], ["c", "z"]]);
    mutants.push(m);
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["nodes"]["p"]["arguments"][3]["renaming"] = json!([["a", "x"]]);
    mutants.push(m);
    let mut m = cyclic_slots(["x", "y", "z"]);
    m["slotted"]["nodes"]["p"]["arguments"]
        .as_array_mut()
        .unwrap()
        .pop();
    mutants.push(m);
    let mut m = ordinary();
    m["nodes"]["p"]["children"] = json!(["missing", "a"]);
    mutants.push(m);
    let mut m = ordinary();
    m["root_eclasses"] = json!(["missing"]);
    mutants.push(m);
    for (i, m) in mutants.into_iter().enumerate() {
        assert!(Graph::try_from(&document(m)).is_err(), "mutant {i}");
    }
}

#[test]
fn verifier_rejects_corrupt_certificates_without_searching() {
    fn parent_node(w: &mut Witness) -> &mut NodeMatch {
        w.classes
            .get_mut(&"P".into())
            .unwrap()
            .nodes
            .get_mut(&"p".into())
            .unwrap()
    }

    let a = graph(cyclic_slots(["x", "y", "z"]));
    let b = graph(cyclic_slots(["y", "z", "x"]));
    let witness = iso(&a, &b);
    let c = egraph_serialize::ClassId::from("C");
    let p = egraph_serialize::ClassId::from("P");
    let mut mutants = Vec::new();
    let mut w = witness.clone();
    w.classes.remove(&c);
    mutants.push(w);
    let mut w = witness.clone();
    w.classes.get_mut(&p).unwrap().target = c.clone();
    mutants.push(w);
    let mut w = witness.clone();
    w.classes.get_mut(&c).unwrap().slots = vec![0, 0, 2];
    mutants.push(w);
    let mut w = witness.clone();
    w.classes.get_mut(&p).unwrap().slots[0] = usize::MAX;
    mutants.push(w);
    let mut w = witness.clone();
    parent_node(&mut w).parent = 1;
    mutants.push(w);
    let mut w = witness.clone();
    parent_node(&mut w).children.clear();
    mutants.push(w);
    let mut w = witness.clone();
    parent_node(&mut w).children = vec![usize::MAX; 2];
    mutants.push(w);
    let mut w = witness.clone();
    parent_node(&mut w).children = vec![0; 2];
    mutants.push(w);
    let mut w = witness;
    parent_node(&mut w).target = "c".into();
    mutants.push(w);
    for (i, w) in mutants.into_iter().enumerate() {
        assert!(verify(&a, &b, &w).is_err(), "witness mutant {i}");
    }
    let a = graph(private_slots(["x", "y"], "x"));
    let b = graph(private_slots(["q", "p"], "z"));
    let mut w = iso(&a, &b);
    w.classes
        .get_mut(&"A".into())
        .unwrap()
        .nodes
        .get_mut(&"a".into())
        .unwrap()
        .locals = vec![0, 0];
    assert!(verify(&a, &b, &w).is_err());
}

#[test]
fn exhaustion_is_inconclusive_and_zero_budget_does_not_claim_a_difference() {
    let a = graph(ordinary());
    for limits in [
        Limits {
            search: 0,
            ..Limits::default()
        },
        Limits {
            node_variants: 0,
            ..Limits::default()
        },
    ] {
        assert!(matches!(
            find_isomorphism(&a, &a, limits).unwrap(),
            Outcome::Inconclusive { .. }
        ));
    }
}

#[test]
fn incremental_group_validation_agrees_with_exhaustive_composition() {
    fn permutations(xs: &mut [usize], start: usize, out: &mut Vec<Vec<usize>>) {
        if start == xs.len() {
            out.push(xs.to_vec());
            return;
        }
        for i in start..xs.len() {
            xs.swap(start, i);
            permutations(xs, start + 1, out);
            xs.swap(start, i);
        }
    }
    for degree in 0..=3 {
        let mut ps = Vec::new();
        permutations(&mut (0..degree).collect::<Vec<_>>(), 0, &mut ps);
        for subset in 0..(1 << ps.len()) {
            let group: BTreeSet<_> = ps
                .iter()
                .enumerate()
                .filter(|(i, _)| subset & (1 << i) != 0)
                .map(|(_, p)| p.clone())
                .collect();
            let expected = group.contains(&(0..degree).collect::<Vec<_>>())
                && group.iter().all(|p| {
                    group
                        .iter()
                        .all(|q| group.contains(&q.iter().map(|&i| p[i]).collect::<Vec<_>>()))
                });
            assert_eq!(graph::closed_group(&group, degree), expected);
        }
    }
}

#[test]
fn long_class_chains_use_an_iterative_search() {
    let mut nodes = BTreeMap::new();
    for i in 0..2000 {
        nodes.insert(format!("n{i:04}"), json!({"op": format!("f{i}"), "eclass": format!("c{i:04}"), "children": if i==0 {vec![]} else {vec![format!("n{:04}",i-1)]}}));
    }
    let a = graph(json!({"nodes":nodes}));
    iso(&a, &a);
}

#[test]
fn annotations_with_no_slots_are_equivalent_to_an_ordinary_graph() {
    let plain = ordinary();
    let mut annotated = plain.clone();
    annotated["slotted"] = json!({
        "classes": {"A":{"slots":[],"group":[[]]},"B":{"slots":[],"group":[[]]},"P":{"slots":[],"group":[[]]}},
        "nodes": {"a":{"arguments":[]},"b":{"arguments":[]},"p":{"arguments":[{"kind":"child","renaming":[]},{"kind":"child","renaming":[]}]}}
    });
    let document = document(annotated);
    let encoded = serde_json::to_value(&document).unwrap();
    // It is still the ordinary egraph-serialize schema; no second graph format.
    let ordinary: egraph_serialize::EGraph = serde_json::from_value(encoded).unwrap();
    assert_eq!(ordinary, document.egraph);
    iso(&graph(plain), &Graph::try_from(&document).unwrap());
}

#[test]
fn parent_symmetries_are_selected_independently_for_each_node() {
    let mut a = private_slots(["a", "b"], "a");
    a["slotted"]["classes"]["A"] = json!({"slots":["a","b"],"group":[[0,1],[1,0]]});
    a["slotted"]["nodes"]["b"]["arguments"] =
        json!([{"kind":"slot","slot":"a"},{"kind":"slot","slot":"b"}]);
    let mut b = a.clone();
    b["slotted"]["nodes"]["a"]["arguments"] =
        json!([{"kind":"slot","slot":"b"},{"kind":"slot","slot":"a"}]);
    let witness = iso(&graph(a), &graph(b));
    assert!(
        witness.classes[&"A".into()]
            .nodes
            .values()
            .any(|n| n.parent != 0)
    );
}

#[test]
fn matching_requires_a_bijection_on_nodes_even_when_each_has_a_candidate() {
    let mut a = private_slots(["a", "a"], "a");
    a["nodes"]["b"]["op"] = json!("bind");
    a["slotted"]["nodes"]["b"]["arguments"] =
        json!([{"kind":"slot","slot":"x"},{"kind":"slot","slot":"y"}]);
    let mut b = a.clone();
    b["slotted"]["nodes"]["b"]["arguments"] =
        json!([{"kind":"slot","slot":"x"},{"kind":"slot","slot":"x"}]);
    different(&graph(a), &graph(b));
}

#[test]
fn ordinary_graph_search_agrees_with_an_exhaustive_permutation_oracle() {
    fn edges(code: usize) -> Vec<usize> {
        (0..4).map(|i| (code >> (2 * i)) & 3).collect()
    }
    fn as_graph(edges: &[usize]) -> Graph {
        let nodes: BTreeMap<_, _> = edges
            .iter()
            .enumerate()
            .map(|(i, j)| {
                (
                    format!("n{i}"),
                    json!({"op":"step","eclass":format!("c{i}"),"children":[format!("n{j}")]}),
                )
            })
            .collect();
        graph(json!({"nodes":nodes}))
    }
    let mut permutations = Vec::new();
    for a in 0..4 {
        for b in 0..4 {
            for c in 0..4 {
                for d in 0..4 {
                    let p = vec![a, b, c, d];
                    if p.iter().collect::<BTreeSet<_>>().len() == 4 {
                        permutations.push(p);
                    }
                }
            }
        }
    }
    for code in 0..256 {
        let a = edges(code);
        for b in [
            edges((code * 73 + 17) % 256),
            a.iter().rev().map(|j| 3 - j).collect(),
        ] {
            let expected = permutations
                .iter()
                .any(|p| (0..4).all(|i| p[a[i]] == b[p[i]]));
            let result = find_isomorphism(&as_graph(&a), &as_graph(&b), Limits::default()).unwrap();
            assert_eq!(
                matches!(result, Outcome::Isomorphic { .. }),
                expected,
                "{a:?} vs {b:?}"
            );
            assert!(!matches!(result, Outcome::Inconclusive { .. }));
        }
    }
}

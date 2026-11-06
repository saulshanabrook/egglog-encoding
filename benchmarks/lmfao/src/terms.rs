//! Read the closed planning terms; scalar lambda bodies stay opaque to planning.

use std::collections::BTreeMap;

use anyhow::{Context, Result, bail, ensure};
use egglog::{
    EGraph, Value,
    sort::{MapContainer, S},
};
use egraph_isomorphism::{AnnotatedEGraph, Argument};

pub type Id = usize;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Term {
    pub op: String,
    pub children: Vec<Id>,
}

#[derive(Default)]
pub struct Terms(pub Vec<Vec<Term>>);

const OPERATORS: &[&str] = &[
    "Program",
    "Pair",
    "Output",
    "AggregateQuery",
    "Region",
    "Neighbor",
    "Cons",
    "Nil",
    "Mask",
    "B0",
    "B1",
    "Weights",
    "WeightOne",
    "Scalar",
    "ComputeView",
    "SharedView",
    "ViewColumn",
];

impl Terms {
    pub fn live(graph: &EGraph, slotted: bool) -> Result<Self> {
        let empty = |v| {
            graph
                .value_to_container::<MapContainer>(v)
                .is_some_and(|m| m.data.is_empty())
        };
        let mut leaders = BTreeMap::<Value, Value>::new();
        if slotted {
            graph.constructor_enodes("RenamesToLeader_0", |row| {
                if empty(row.children[1]) {
                    leaders
                        .entry(row.children[0])
                        .and_modify(|v| *v = (*v).min(row.children[2]))
                        .or_insert(row.children[2]);
                }
            })?;
        } else {
            for &op in OPERATORS.iter().chain(std::iter::once(&"Symbol")) {
                graph.constructor_enodes(op, |row| {
                    leaders.insert(row.eclass, row.eclass);
                    if op != "Symbol" {
                        for &child in row.children {
                            leaders.insert(child, child);
                        }
                    }
                })?;
            }
        }
        let mut ids = BTreeMap::new();
        for (&value, &leader) in &leaders {
            ensure!(
                leaders.get(&leader) == Some(&leader),
                "unfinished slotted leader maintenance"
            );
            let next = ids.len();
            ids.entry(value).or_insert(next);
        }
        let canonical = |v| -> Result<Id> {
            Ok(ids[leaders
                .get(&v)
                .ok_or_else(|| anyhow::anyhow!("expected closed planning term"))?])
        };
        let mut result = Self(vec![vec![]; ids.len()]);
        for &op in OPERATORS.iter().chain(std::iter::once(&"Symbol")) {
            let mut error = None;
            graph.constructor_enodes(op, |row| {
                if row.subsumed {
                    return;
                }
                let read = || -> Result<(Id, Term)> {
                    let class = canonical(row.eclass)?;
                    if op == "Symbol" {
                        return Ok((
                            class,
                            Term {
                                op: format!(
                                    "sym:{}",
                                    graph.value_to_base::<S>(row.children[0]).into_inner()
                                ),
                                children: vec![],
                            },
                        ));
                    }
                    if !slotted {
                        let children = if op == "Scalar" {
                            vec![]
                        } else {
                            row.children
                                .iter()
                                .map(|&c| canonical(c))
                                .collect::<Result<_>>()?
                        };
                        return Ok((
                            class,
                            Term {
                                op: op.into(),
                                children,
                            },
                        ));
                    }
                    ensure!(
                        row.children.len().is_multiple_of(2),
                        "invalid closed constructor layout"
                    );
                    let mut children = Vec::new();
                    for pair in row.children.chunks_exact(2) {
                        ensure!(empty(pair[0]), "planning edges must have empty slot maps");
                        if op != "Scalar" {
                            children.push(canonical(pair[1])?);
                        }
                    }
                    Ok((
                        class,
                        Term {
                            op: op.into(),
                            children,
                        },
                    ))
                };
                match read() {
                    Ok((class, term)) => result.0[class].push(term),
                    Err(e) => error = Some(e),
                }
            })?;
            if let Some(error) = error {
                return Err(error);
            }
        }
        result.deduplicate();
        Ok(result)
    }

    // The native reference remains a separate process. Its diagnostic export
    // feeds the same planner; egglog uses live constructor tables above.
    pub fn exported(source: &str) -> Result<Self> {
        let doc: AnnotatedEGraph = serde_json::from_str(source)?;
        let slots = doc.slotted.context("expected slotted graph annotations")?;
        let mut ids = BTreeMap::new();
        for node in doc.egraph.nodes.values() {
            let next = ids.len();
            ids.entry(&node.eclass).or_insert(next);
        }
        let mut result = Self(vec![vec![]; ids.len()]);
        for (id, node) in doc.egraph.nodes.iter().filter(|(_, n)| !n.subsumed) {
            if !OPERATORS.contains(&node.op.as_str()) && !node.op.starts_with("sym:") {
                continue;
            }
            ensure!(
                slots
                    .classes
                    .get(&node.eclass)
                    .is_some_and(|c| c.slots.is_empty()),
                "expected closed planning class"
            );
            ensure!(
                slots
                    .nodes
                    .get(id)
                    .is_some_and(|n| n.arguments.len() == node.children.len()
                        && n.arguments.iter().all(
                            |a| matches!(a, Argument::Child { renaming } if renaming.is_empty())
                        )),
                "planning edges must have empty slot maps"
            );
            let children = if node.op == "Scalar" {
                vec![]
            } else {
                node.children
                    .iter()
                    .map(|id| {
                        doc.egraph
                            .nodes
                            .get(id)
                            .map(|n| ids[&n.eclass])
                            .ok_or_else(|| anyhow::anyhow!("dangling graph edge"))
                    })
                    .collect::<Result<_>>()?
            };
            result.0[ids[&node.eclass]].push(Term {
                op: node.op.clone(),
                children,
            });
        }
        result.deduplicate();
        Ok(result)
    }

    fn deduplicate(&mut self) {
        for nodes in &mut self.0 {
            nodes.sort();
            nodes.dedup();
        }
    }

    pub fn one(&self, class: Id, ops: &[&str]) -> Result<&Term> {
        let nodes: Vec<_> = self.0[class]
            .iter()
            .filter(|n| ops.contains(&n.op.as_str()))
            .collect();
        ensure!(
            nodes.len() == 1,
            "expected one {ops:?} in class {class}, got {}",
            nodes.len()
        );
        Ok(nodes[0])
    }

    pub fn symbol(&self, class: Id) -> Result<&str> {
        let names: Vec<_> = self.0[class]
            .iter()
            .filter_map(|n| n.op.strip_prefix("sym:"))
            .collect();
        ensure!(names.len() == 1, "expected one symbol");
        Ok(names[0])
    }

    pub fn bits(&self, class: Id) -> Result<(u64, u32)> {
        let n = self.one(
            class,
            &["Mask", "B0", "B1", "Weights", "WeightOne", "Scalar"],
        )?;
        if matches!(n.op.as_str(), "Mask" | "Weights") {
            let [a, b] = n.children[..] else {
                bail!("invalid vector")
            };
            let ((a, wa), (b, wb)) = (self.bits(a)?, self.bits(b)?);
            ensure!(wa + wb <= 64, "planning masks support at most 64 entries");
            Ok((a | (b << wa), wa + wb))
        } else {
            Ok((u64::from(matches!(n.op.as_str(), "B1" | "Scalar")), 1))
        }
    }

    pub fn list(&self, mut class: Id) -> Result<Vec<Id>> {
        let mut result = Vec::new();
        loop {
            let n = self.one(class, &["Cons", "Nil"])?;
            if n.op == "Nil" {
                return Ok(result);
            }
            let [head, tail] = n.children[..] else {
                bail!("invalid list")
            };
            result.push(head);
            class = tail;
        }
    }
}

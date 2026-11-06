//! Cost-based extraction for the fixed LMFAO join-tree case study.

mod dag;
mod terms;

use anyhow::{Result, bail, ensure};
use serde::Serialize;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use terms::{Id, Terms};

#[derive(Clone, Debug)]
struct Region {
    origin: usize,
    destination: usize,
    attributes: u64,
    functions: u64,
    local: u64,
    children: Vec<(Id, u64)>,
}

#[derive(Clone, Debug)]
struct Column {
    weights: u64,
    local: u64,
    incoming: Vec<Id>,
    producer: Option<Id>,
}

#[derive(Clone, Debug)]
struct Alternative {
    region: Id,
    keys: u64,
    column: Option<Column>,
}

impl Alternative {
    fn dependencies(&self) -> Vec<Id> {
        self.column
            .as_ref()
            .map(|c| c.incoming.iter().copied().chain(c.producer).collect())
            .unwrap_or_default()
    }
}

/// Executable alternatives read from the live egraph or the native reference export.
/// Scalar functions are the immutable, indexed kernels supplied by the frontend.
struct Planner {
    regions: BTreeMap<Id, Region>,
    options: BTreeMap<Id, Vec<Alternative>>,
    roots: Vec<Id>,
}

impl Planner {
    fn read(terms: &Terms) -> Result<Self> {
        let workload: Json = serde_json::from_str(include_str!("../workload.json"))?;
        let tables: Vec<_> = workload["relations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| r["name"].as_str().unwrap())
            .collect();
        let relation = |id| -> Result<usize> {
            let name = terms.symbol(id)?;
            tables
                .iter()
                .position(|&s| s == name)
                .ok_or_else(|| anyhow::anyhow!("unknown relation {name}"))
        };
        let mut regions = BTreeMap::new();
        for (id, nodes) in terms.0.iter().enumerate() {
            for n in nodes.iter().filter(|n| n.op == "Region") {
                let [origin, destination, attrs, functions, local, children] = n.children[..]
                else {
                    bail!("invalid Region")
                };
                let children = terms
                    .list(children)?
                    .into_iter()
                    .map(|c| {
                        let n = terms.one(c, &["Neighbor"])?;
                        let [region, separator] = n.children[..] else {
                            bail!("invalid Neighbor")
                        };
                        Ok((region, terms.bits(separator)?.0))
                    })
                    .collect::<Result<_>>()?;
                ensure!(
                    regions
                        .insert(
                            id,
                            Region {
                                origin: relation(origin)?,
                                destination: relation(destination)?,
                                attributes: terms.bits(attrs)?.0,
                                functions: terms.bits(functions)?.0,
                                local: terms.bits(local)?.0,
                                children
                            }
                        )
                        .is_none(),
                    "ambiguous region"
                );
            }
        }
        let programs: Vec<_> = terms
            .0
            .iter()
            .flatten()
            .filter(|n| n.op == "Program")
            .collect();
        ensure!(programs.len() == 1, "expected one Program");
        let mut outputs = BTreeMap::new();
        let mut pending = programs[0].children.clone();
        while let Some(class) = pending.pop() {
            let n = terms.one(class, &["Pair", "Output"])?;
            if n.op == "Pair" {
                pending.extend(&n.children);
                continue;
            }
            let [label, root] = n.children[..] else {
                bail!("invalid Output")
            };
            let query: usize = terms
                .symbol(label)?
                .strip_prefix('q')
                .ok_or_else(|| anyhow::anyhow!("invalid query label"))?
                .parse()?;
            ensure!(outputs.insert(query, root).is_none(), "duplicate query");
        }
        ensure!(
            outputs.keys().copied().eq(0..outputs.len()),
            "missing query output"
        );
        let roots: Vec<_> = outputs.into_values().collect();
        let mut options = BTreeMap::new();
        let mut pending = roots.clone();
        while let Some(class) = pending.pop() {
            if options.contains_key(&class) {
                continue;
            }
            let mut alternatives = Vec::new();
            for n in &terms.0[class] {
                let (region, keys, column) = match n.op.as_str() {
                    "SharedView" => {
                        let [region, keys] = n.children[..] else {
                            bail!("invalid SharedView")
                        };
                        (region, keys, None)
                    }
                    "ComputeView" | "ViewColumn" => {
                        let (region, keys, weights, local, children, producer) = if n.op
                            == "ComputeView"
                        {
                            let [region, keys, weights, local, children] = n.children[..] else {
                                bail!("invalid ComputeView")
                            };
                            (region, keys, weights, local, children, None)
                        } else {
                            let [producer, weights, local, children] = n.children[..] else {
                                bail!("invalid ViewColumn")
                            };
                            let [region, keys] = terms.one(producer, &["SharedView"])?.children[..]
                            else {
                                bail!("invalid producer")
                            };
                            (region, keys, weights, local, children, Some(producer))
                        };
                        (
                            region,
                            keys,
                            Some(Column {
                                weights: terms.bits(weights)?.0,
                                local: terms.bits(local)?.0,
                                incoming: terms.list(children)?,
                                producer,
                            }),
                        )
                    }
                    _ => continue,
                };
                let option = Alternative {
                    region,
                    keys: terms.bits(keys)?.0,
                    column,
                };
                pending.extend(option.dependencies());
                alternatives.push(option);
            }
            ensure!(
                !alternatives.is_empty(),
                "no executable alternative; increase rewrite budget"
            );
            options.insert(class, alternatives);
        }
        let result = Self {
            regions,
            options,
            roots,
        };
        for &root in &result.roots {
            let [_, keys, weights] = terms.one(root, &["AggregateQuery"])?.children[..] else {
                bail!("invalid query")
            };
            for v in &result.options[&root] {
                let c = v
                    .column
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("query lacks a column"))?;
                let r = &result.regions[&v.region];
                ensure!(
                    (v.keys, c.weights) == (terms.bits(keys)?.0, terms.bits(weights)?.0)
                        && r.origin == r.destination,
                    "alternative changes query"
                );
            }
        }
        result.validate()?;
        Ok(result)
    }

    fn validate(&self) -> Result<()> {
        for v in self.options.values().flatten() {
            let Some(c) = &v.column else {
                continue;
            };
            let r = &self.regions[&v.region];
            ensure!(
                c.local == c.weights & r.local && c.incoming.len() == r.children.len(),
                "invalid local kernel or child count"
            );
            for (&child, &(region, separator)) in c.incoming.iter().zip(&r.children) {
                let r = &self.regions[&region];
                for v2 in &self.options[&child] {
                    let c2 = v2
                        .column
                        .as_ref()
                        .ok_or_else(|| anyhow::anyhow!("child lacks column"))?;
                    ensure!(
                        (v2.region, v2.keys, c2.weights)
                            == (
                                region,
                                separator | (v.keys & r.attributes),
                                c.weights & r.functions
                            ),
                        "invalid aggregate pushdown"
                    );
                }
            }
        }
        Ok(())
    }

    fn cost(&self, v: &Alternative) -> u64 {
        let base =
            1 + self.regions[&v.region].children.len() as u64 + u64::from(v.keys.count_ones());
        match &v.column {
            None => base,
            Some(c) => {
                2 + u64::from(c.local.count_ones()) + if c.producer.is_none() { base } else { 0 }
            }
        }
    }

    // Every directional child is a smaller subtree. Check that property at the
    // dependency level instead of adding generic cycle-elimination MILP variables.
    fn order(&self, selection: Option<&BTreeMap<Id, usize>>) -> Result<Vec<Id>> {
        fn visit(
            g: &Planner,
            c: Id,
            selection: Option<&BTreeMap<Id, usize>>,
            states: &mut BTreeMap<Id, bool>,
            order: &mut Vec<Id>,
        ) -> Result<()> {
            if let Some(&done) = states.get(&c) {
                ensure!(done, "cyclic planning alternatives");
                return Ok(());
            }
            states.insert(c, false);
            let options = g
                .options
                .get(&c)
                .ok_or_else(|| anyhow::anyhow!("missing dependency"))?;
            let choices: &[Alternative] = if let Some(selected) = selection {
                let i = *selected
                    .get(&c)
                    .ok_or_else(|| anyhow::anyhow!("incomplete selection"))?;
                std::slice::from_ref(
                    options
                        .get(i)
                        .ok_or_else(|| anyhow::anyhow!("invalid selection"))?,
                )
            } else {
                options
            };
            for v in choices {
                for child in v.dependencies() {
                    visit(g, child, selection, states, order)?;
                }
            }
            states.insert(c, true);
            order.push(c);
            Ok(())
        }
        let mut states = BTreeMap::new();
        let mut order = Vec::new();
        for &c in &self.roots {
            visit(self, c, selection, &mut states, &mut order)?;
        }
        Ok(order)
    }

    fn score(&self, selected: &BTreeMap<Id, usize>) -> Result<u64> {
        Ok(self
            .order(Some(selected))?
            .iter()
            .map(|c| self.cost(&self.options[c][selected[c]]))
            .sum())
    }

    fn plan(&self, selected: &BTreeMap<Id, usize>) -> Result<Json> {
        let mut views = Vec::<Json>::new();
        let mut producers = BTreeMap::new();
        let mut columns = BTreeMap::new();
        for class in self.order(Some(selected))? {
            let v = &self.options[&class][selected[&class]];
            let Some(c) = &v.column else {
                continue;
            };
            let index = *producers.entry(c.producer.unwrap_or(class)).or_insert_with(|| {
                let r = &self.regions[&v.region];
                views.push(json!({"origin": r.origin, "destination": r.destination, "keys": indices(v.keys), "aggregates": []}));
                views.len() - 1
            });
            let incoming: Vec<_> = c.incoming.iter().map(|child| columns[child]).collect();
            let aggregates = views[index]["aggregates"].as_array_mut().unwrap();
            columns.insert(class, (index, aggregates.len()));
            aggregates.push(json!({"functions": indices(c.local), "incoming": incoming}));
        }
        let outputs: Vec<_> = self
            .roots
            .iter()
            .map(|c| {
                let (view, aggregate) = columns[c];
                json!({"view": view, "aggregate": aggregate, "root": views[view]["origin"]})
            })
            .collect();
        Ok(json!({"views": views, "outputs": outputs}))
    }
}

fn indices(mask: u64) -> Vec<usize> {
    (0..64).filter(|i| mask & (1 << i) != 0).collect()
}

/// Selected LMFAO plan and the solver's objective, bound and phase information.
#[derive(Serialize)]
pub struct Extraction {
    pub plan: Json,
    pub report: Json,
}

/// Extract directly from an evaluated slotted egraph's closed planning tables.
/// Inputs must come from the pinned workload translator and logical.egg rules:
/// scalar kernels are opaque, immutable functions identified by vector position.
pub fn extract_live(graph: &egglog::EGraph, timeout: f64) -> Result<Extraction> {
    extract(Terms::live(graph, true)?, timeout)
}

/// Extract the same planning IR from ordinary egglog with names as constructor data.
/// Requires the same generated-input and immutable-kernel contract as extract_live.
pub fn extract_plain(graph: &egglog::EGraph, timeout: f64) -> Result<Extraction> {
    extract(Terms::live(graph, false)?, timeout)
}

/// Extract from the native reference's annotated graph export.
/// Requires the same generated-input and immutable-kernel contract as extract_live.
pub fn extract_export(source: &str, timeout: f64) -> Result<Extraction> {
    extract(Terms::exported(source)?, timeout)
}

fn extract(terms: Terms, timeout: f64) -> Result<Extraction> {
    ensure!(
        timeout.is_finite() && timeout > 0.0,
        "DAG timeout must be finite and positive"
    );
    let planner = Planner::read(&terms)?;
    let (selected, report) = dag::solve(&planner, timeout)?;
    Ok(Extraction {
        plan: planner.plan(&selected)?,
        report,
    })
}

//! Export the logical slotted graph directly from a live egglog database.
//!
//! Native table reads have no visualization limits. We validate raw edges before
//! changing frames or replacing binder edges with slot literals, since those
//! operations could otherwise hide malformed rows. Every constructor row survives
//! export, including duplicates that coincide after frame translation.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;

use egglog::{
    CommandOutput, EGraph, UserDefinedCommand, Value,
    ast::{Expr, Literal},
    sort::{MapContainer, S, SetContainer},
};
use egraph_isomorphism::{
    AnnotatedEGraph, Argument, ClassSlots, Graph, NodeSlots, Slotted,
    egraph_serialize::{ClassData, ClassId, Node, NodeId},
};
use serde::Serialize;

use super::{
    layout::Layouts,
    model::{Column, Constructor, Symbols},
};

type Map = BTreeMap<i64, i64>;

/// Counts taken before constructing the serialized document. Node counts come
/// from native table sizes, independently of row reconstruction.
#[derive(Debug, Serialize)]
pub struct Counts {
    /// Connected components of the recorded leader relations.
    pub classes: usize,
    /// Sum of native constructor table sizes, including the variable constructor.
    pub nodes: usize,
}

/// An annotated egraph-serialize document with independently collected counts.
/// The extra `counts` field is ignored by consumers of [`AnnotatedEGraph`].
#[derive(Debug, Serialize)]
pub struct Export {
    /// The logical graph, with slot and symmetry annotations.
    #[serde(flatten)]
    pub graph: AnnotatedEGraph,
    /// Sizes collected independently of serialization.
    pub counts: Counts,
}

/// Explicit operator correspondence for comparisons with an untyped reference.
#[derive(Clone, Debug)]
pub enum OperatorName {
    /// Replace the constructor name. The constructor must have no payloads.
    Operator(String),
    /// Use a single literal payload, preceded by this prefix, as the operator.
    Payload(String),
}

/// Export all declared slotted carriers, preserving their sorts and source labels.
/// Does not run rules, repair groups, or mutate the graph. Run slotted maintenance
/// before exporting; inconsistent or unfinished invariants are errors.
pub fn export(graph: &EGraph) -> Result<Export, String> {
    export_named(graph, &BTreeMap::new())
}

/// Export using a complete constructor correspondence for a single untyped carrier.
/// An empty correspondence uses source labels and retains sorts, as [`export`] does.
/// A nonempty correspondence must cover every declared source constructor; it changes
/// operator spellings and omits the single carrier's sort, but preserves all rows.
pub fn export_named(
    graph: &EGraph,
    names: &BTreeMap<String, OperatorName>,
) -> Result<Export, String> {
    let layouts = Layouts::load(graph)?;
    if !names.is_empty()
        && (layouts.carriers.len() != 1 || names.keys().ne(layouts.constructors.keys()))
    {
        return Err("reference names must cover every constructor of exactly one carrier".into());
    }
    let mut out = Export {
        graph: AnnotatedEGraph {
            slotted: Some(Slotted::default()),
            ..Default::default()
        },
        counts: Counts {
            classes: 0,
            nodes: 0,
        },
    };
    for symbols in &layouts.carriers {
        let snapshot = Snapshot::read(graph, symbols, &layouts.constructors, names)?;
        out.counts.nodes += snapshot.raw_nodes;
        out.counts.classes += snapshot.append(&mut out.graph, &symbols.sort, names.is_empty())?;
    }
    if out.counts.nodes != out.graph.egraph.nodes.len() {
        return Err(format!(
            "raw constructor count {} disagrees with exported graph {}",
            out.counts.nodes,
            out.graph.egraph.nodes.len()
        ));
    }
    // This checks the recorded full groups for identity/closure, exact edge domains,
    // dangling children, and annotation coverage. Never synthesize missing elements.
    Graph::try_from(&out.graph).map_err(|e| e.to_string())?;
    Ok(out)
}

#[derive(Clone, Debug)]
struct Edge {
    class: Value,
    map: Map,
}

#[derive(Clone, Debug)]
struct Row {
    class: Value,
    label: String,
    edges: Vec<Edge>,
    binders: Vec<usize>,
    covered: Option<usize>,
    variable: bool,
    subsumed: bool,
}

#[derive(Clone, Debug)]
struct Link {
    source: Value,
    map: Map,
    target: Value,
}

/// Raw carrier values and their recorded invariants, before any projection.
#[derive(Clone)]
struct Snapshot {
    slots: BTreeMap<Value, Map>,
    links: Vec<Link>,
    groups: BTreeMap<Value, Vec<Map>>,
    rows: Vec<Row>,
    variable: Value,
    raw_nodes: usize,
}

fn renaming(graph: &EGraph, value: Value) -> Result<Map, String> {
    let map = graph
        .value_to_container::<MapContainer>(value)
        .ok_or("missing renaming container")?;
    if map.rebuilds_contents() {
        return Err("renaming contains non-slot values".into());
    }
    let map: Map = map
        .data
        .iter()
        .map(|(a, b)| {
            (
                graph.value_to_base::<i64>(*a),
                graph.value_to_base::<i64>(*b),
            )
        })
        .collect();
    if map.values().collect::<BTreeSet<_>>().len() != map.len() {
        return Err("non-injective renaming".into());
    }
    Ok(map)
}

fn compose(a: &Map, b: &Map) -> Map {
    b.iter()
        .filter_map(|(k, v)| a.get(v).map(|image| (*k, *image)))
        .collect()
}

fn inverse(map: &Map) -> Map {
    map.iter().map(|(a, b)| (*b, *a)).collect()
}

impl Snapshot {
    fn read(
        graph: &EGraph,
        symbols: &Symbols,
        constructors: &BTreeMap<String, Constructor>,
        names: &BTreeMap<String, OperatorName>,
    ) -> Result<Self, String> {
        let mut slots = BTreeMap::new();
        let mut links = Vec::new();
        let mut groups = BTreeMap::new();
        let mut error = None;
        graph
            .function_entries(&symbols.free_vars, |row| {
                match renaming(graph, row.output) {
                    Ok(map) if map.iter().all(|(a, b)| a == b) => {
                        slots.insert(row.inputs[0], map);
                    }
                    Ok(_) => error = Some("FreeVars is not an identity map".into()),
                    Err(e) => error = Some(e),
                }
            })
            .map_err(|e| e.to_string())?;
        graph
            .constructor_enodes(&symbols.renames, |row| {
                match renaming(graph, row.children[1]) {
                    Ok(map) => links.push(Link {
                        source: row.children[0],
                        map,
                        target: row.children[2],
                    }),
                    Err(e) => error = Some(e),
                }
            })
            .map_err(|e| e.to_string())?;
        graph
            .function_entries(&symbols.group, |row| {
                let Some(group) = graph.value_to_container::<SetContainer>(row.output) else {
                    error = Some("missing group container".into());
                    return;
                };
                let permutations = groups.entry(row.inputs[0]).or_insert_with(Vec::new);
                for value in group.data.iter() {
                    match renaming(graph, *value) {
                        Ok(map) => permutations.push(map),
                        Err(e) => error = Some(e),
                    }
                }
            })
            .map_err(|e| e.to_string())?;
        let mut rows = Vec::new();
        graph
            .constructor_enodes(&symbols.var, |row| {
                if graph.value_to_base::<i64>(row.children[0]) != 0 {
                    error = Some("variable payload must be canonical slot 0".into());
                }
                rows.push(Row {
                    class: row.eclass,
                    label: "var".into(),
                    edges: vec![],
                    binders: vec![],
                    covered: None,
                    variable: true,
                    subsumed: row.subsumed,
                });
            })
            .map_err(|e| e.to_string())?;
        if rows.len() != 1 {
            return Err(format!(
                "expected one raw variable row, found {}",
                rows.len()
            ));
        }
        let variable = rows[0].class;
        let mut raw_nodes = graph.get_size(&symbols.var);
        for op in constructors.values().filter(|op| op.sort == symbols.sort) {
            raw_nodes += graph.get_size(&op.name);
            let spelling = names.get(&op.name);
            graph
                .constructor_enodes(&op.name, |row| {
                    match read_row(graph, op, row.eclass, row.children, row.subsumed, spelling) {
                        Ok(row) => rows.push(row),
                        Err(e) => error = Some(e),
                    }
                })
                .map_err(|e| e.to_string())?;
        }
        if let Some(error) = error {
            return Err(error);
        }
        Ok(Self {
            slots,
            links,
            groups,
            rows,
            variable,
            raw_nodes,
        })
    }

    /// Form connected components of all leader links, including partial ones.
    /// A frame maps representative live slots into a member's local slot names.
    /// Validate every frame as a bijection before composing any node edge with it.
    fn append(&self, out: &mut AnnotatedEGraph, sort: &str, typed: bool) -> Result<usize, String> {
        let mut adjacency = BTreeMap::<Value, Vec<(&Link, bool)>>::new();
        for &class in self.slots.keys() {
            adjacency.entry(class).or_default();
        }
        for row in &self.rows {
            adjacency.entry(row.class).or_default();
            for edge in &row.edges {
                adjacency.entry(edge.class).or_default();
            }
        }
        for link in &self.links {
            adjacency
                .entry(link.source)
                .or_default()
                .push((link, false));
            adjacency.entry(link.target).or_default().push((link, true));
        }
        for &class in self.groups.keys() {
            adjacency.entry(class).or_default();
        }
        if let Some(class) = adjacency.keys().find(|c| !self.slots.contains_key(c)) {
            return Err(format!("{class:?}: no FreeVars row"));
        }
        let mut reps = BTreeMap::new();
        let mut frames = BTreeMap::new();
        let mut components = Vec::new();
        for &start in adjacency.keys() {
            if reps.contains_key(&start) {
                continue;
            }
            let mut members = BTreeSet::from([start]);
            let mut queue = vec![start];
            let mut i = 0;
            while i < queue.len() {
                for (link, forward) in &adjacency[&queue[i]] {
                    let other = if *forward { link.source } else { link.target };
                    if members.insert(other) {
                        queue.push(other);
                    }
                }
                i += 1;
            }
            let rep = *members
                .iter()
                .max_by_key(|c| (self.slots[c].len(), std::cmp::Reverse(**c)))
                .unwrap();
            for member in &members {
                reps.insert(*member, rep);
            }
            frames.insert(rep, self.slots[&rep].clone());
            queue = vec![rep];
            i = 0;
            while i < queue.len() {
                let class = queue[i];
                for (link, forward) in &adjacency[&class] {
                    let other = if *forward { link.source } else { link.target };
                    if frames.contains_key(&other) {
                        continue;
                    }
                    let map = if *forward {
                        link.map.clone()
                    } else {
                        inverse(&link.map)
                    };
                    frames.insert(other, compose(&map, &frames[&class]));
                    queue.push(other);
                }
                i += 1;
            }
            for member in members {
                let frame = &frames[&member];
                if frame.keys().ne(self.slots[&rep].keys())
                    || frame.values().copied().collect::<BTreeSet<_>>()
                        != self.slots[&member].keys().copied().collect()
                    || inverse(frame).len() != frame.len()
                {
                    return Err(format!("{member:?}: frame is not a bijection"));
                }
            }
            components.push(rep);
        }
        self.validate_rows(&reps)?;
        let up: BTreeMap<_, _> = frames.iter().map(|(c, m)| (*c, inverse(m))).collect();
        let mut groups: BTreeMap<Value, BTreeSet<Map>> =
            components.iter().map(|c| (*c, BTreeSet::new())).collect();
        for (&class, permutations) in &self.groups {
            for permutation in permutations {
                if permutation.keys().ne(self.slots[&class].keys())
                    || permutation.values().copied().collect::<BTreeSet<_>>()
                        != self.slots[&class].keys().copied().collect()
                {
                    return Err("recorded group element is not a permutation of FreeVars".into());
                }
                let rep = reps[&class];
                let sym = compose(&up[&class], &compose(permutation, &frames[&class]));
                if sym.keys().ne(self.slots[&rep].keys())
                    || sym.values().copied().collect::<BTreeSet<_>>()
                        != self.slots[&rep].keys().copied().collect()
                {
                    return Err("framed symmetry is not a permutation".into());
                }
                groups.get_mut(&rep).unwrap().insert(sym);
            }
        }
        for link in &self.links {
            let relative = compose(
                &up[&link.source],
                &compose(&link.map, &frames[&link.target]),
            );
            if !groups[&reps[&link.source]].contains(&relative) {
                return Err("leader relation is inconsistent with recorded symmetry group".into());
            }
        }
        let class_id = |class| ClassId::from(format!("{sort}-{class:?}"));
        let slotted = out.slotted.as_mut().unwrap();
        for &rep in &components {
            let slots: Vec<_> = self.slots[&rep].keys().copied().collect();
            let positions: BTreeMap<_, _> =
                slots.iter().enumerate().map(|(i, s)| (*s, i)).collect();
            slotted.classes.insert(
                class_id(rep),
                ClassSlots {
                    slots: slots.iter().map(ToString::to_string).collect(),
                    group: groups[&rep]
                        .iter()
                        .map(|m| slots.iter().map(|s| positions[&m[s]]).collect())
                        .collect(),
                },
            );
            out.egraph.class_data.insert(
                class_id(rep),
                ClassData {
                    typ: typed.then(|| sort.to_owned()),
                    extra: Default::default(),
                },
            );
        }
        let node_ids: Vec<_> = (0..self.rows.len())
            .map(|i| NodeId::from(format!("{sort}/n{i}")))
            .collect();
        let mut representative_nodes = BTreeMap::new();
        for (row, id) in self.rows.iter().zip(&node_ids) {
            representative_nodes
                .entry(reps[&row.class])
                .or_insert(id.clone());
        }
        for (row, id) in self.rows.iter().zip(node_ids) {
            // Live names and private names use disjoint spellings. The private
            // spelling preserves equality within this row; its scope is node-local.
            let slot = |s| {
                up[&row.class]
                    .get(&s)
                    .map(ToString::to_string)
                    .unwrap_or_else(|| format!("private:{s}"))
            };
            let mut arguments = Vec::new();
            let mut children = Vec::new();
            if row.variable {
                arguments.push(Argument::Slot { slot: slot(0) });
            }
            for (i, edge) in row.edges.iter().enumerate() {
                if row.binders.contains(&i) {
                    // Validate the raw {0 -> bound} edge first, then preserve the
                    // actual bound name even when the variable class has lost slot 0.
                    arguments.push(Argument::Slot {
                        slot: slot(edge.map[&0]),
                    });
                } else {
                    let rep = reps[&edge.class];
                    let child = representative_nodes
                        .get(&rep)
                        .ok_or("child class has no constructor row")?;
                    children.push(child.clone());
                    arguments.push(Argument::Child {
                        renaming: compose(&edge.map, &frames[&edge.class])
                            .iter()
                            .map(|(a, b)| (a.to_string(), slot(*b)))
                            .collect(),
                    });
                }
            }
            out.egraph.nodes.insert(
                id.clone(),
                Node {
                    op: row.label.clone(),
                    children,
                    eclass: class_id(reps[&row.class]),
                    cost: 1.0.try_into().unwrap(),
                    subsumed: row.subsumed,
                },
            );
            slotted.nodes.insert(id, NodeSlots { arguments });
        }
        Ok(components.len())
    }

    /// Check the original edge domains and binder targets before projection can
    /// discard them. A node's free slots must contain its class's live slots.
    fn validate_rows(&self, reps: &BTreeMap<Value, Value>) -> Result<(), String> {
        for row in &self.rows {
            let mut free = BTreeSet::new();
            let mut bound = BTreeSet::new();
            if row.variable {
                free.insert(0);
            }
            for &i in &row.binders {
                let edge = &row.edges[i];
                if edge.map.keys().copied().collect::<Vec<_>>() != [0]
                    || reps[&edge.class] != reps[&self.variable]
                {
                    return Err(
                        "binder must point to the variable class with exactly domain {0}".into(),
                    );
                }
                bound.insert(edge.map[&0]);
            }
            for (i, edge) in row.edges.iter().enumerate() {
                if row.binders.contains(&i) {
                    continue;
                }
                if edge.map.keys().ne(self.slots[&edge.class].keys()) {
                    return Err("edge domain differs from child FreeVars".into());
                }
                free.extend(
                    edge.map
                        .values()
                        .filter(|s| Some(i) != row.covered || !bound.contains(s))
                        .copied(),
                );
            }
            if !self.slots[&row.class].keys().all(|s| free.contains(s)) {
                return Err(format!(
                    "{}: class slots are not contained in node free slots",
                    row.label
                ));
            }
        }
        Ok(())
    }
}

fn read_row(
    graph: &EGraph,
    op: &Constructor,
    class: Value,
    values: &[Value],
    subsumed: bool,
    name: Option<&OperatorName>,
) -> Result<Row, String> {
    let mut edges = Vec::new();
    let mut payloads = Vec::new();
    let mut column = 0;
    for kind in &op.columns {
        match kind {
            Column::Payload(sort) => {
                payloads.push(match sort.as_str() {
                    "i64" => Literal::Int(graph.value_to_base::<i64>(values[column])),
                    "String" => {
                        Literal::String(graph.value_to_base::<S>(values[column]).into_inner())
                    }
                    _ => return Err(format!("unsupported payload sort {sort}")),
                });
                column += 1;
            }
            _ => {
                edges.push(Edge {
                    class: values[column + 1],
                    map: renaming(graph, values[column])?,
                });
                column += 2;
            }
        }
    }
    let label = match name {
        Some(OperatorName::Operator(name)) if payloads.is_empty() => name.clone(),
        Some(OperatorName::Payload(prefix)) if payloads.len() == 1 && edges.is_empty() => {
            let text = match &payloads[0] {
                Literal::String(s) => s.clone(),
                value => value.to_string(),
            };
            format!("{prefix}{text}")
        }
        Some(_) => {
            return Err(format!(
                "reference name does not fit payload layout of {}",
                op.name
            ));
        }
        None if payloads.is_empty() => op.name.clone(),
        None => format!(
            "({} {})",
            op.name,
            payloads
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        ),
    };
    Ok(Row {
        class,
        label,
        edges,
        binders: op.binders(),
        covered: op.covered(),
        variable: false,
        subsumed,
    })
}

/// `(slotted-export "path" (Constructor "tag") (Literal "=payload" "prefix") ...)`.
/// Correspondences are optional; the ordinary export preserves source names/types.
pub(super) struct ExportCommand;

impl UserDefinedCommand for ExportCommand {
    fn update(
        &self,
        graph: &mut EGraph,
        args: &[Expr],
    ) -> Result<Vec<CommandOutput>, egglog::Error> {
        let run = || -> Result<(), String> {
            let string = |e: &Expr| match e {
                Expr::Lit(_, Literal::String(s)) => Ok(s.clone()),
                _ => Err("slotted-export expects string literals".to_owned()),
            };
            let path = string(
                args.first()
                    .ok_or("slotted-export expects an output path")?,
            )?;
            let mut names = BTreeMap::new();
            for arg in &args[1..] {
                let Expr::Call(_, ctor, args) = arg else {
                    return Err("expected (Constructor \"name\")".into());
                };
                let tag = string(args.first().ok_or("missing operator name")?)?;
                let name = if tag == "=payload" && (1..=2).contains(&args.len()) {
                    OperatorName::Payload(args.get(1).map(string).transpose()?.unwrap_or_default())
                } else if args.len() == 1 {
                    OperatorName::Operator(tag)
                } else {
                    return Err("invalid operator correspondence".into());
                };
                if names.insert(ctor.clone(), name).is_some() {
                    return Err(format!("duplicate correspondence for {ctor}"));
                }
            }
            let export = export_named(graph, &names)?;
            let file = std::fs::File::create(path).map_err(|e| e.to_string())?;
            let mut writer = std::io::BufWriter::new(file);
            serde_json::to_writer(&mut writer, &export).map_err(|e| e.to_string())?;
            writer.flush().map_err(|e| e.to_string())
        };
        run().map_err(|e| egglog::Error::BackendError(format!("slotted export: {e}")))?;
        Ok(vec![])
    }
}

#[cfg(test)]
mod tests;

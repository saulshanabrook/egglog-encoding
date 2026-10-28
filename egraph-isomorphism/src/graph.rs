//! Validate the serialized document and assign dense indices for comparison.
//!
//! Node children in egraph-serialize point to representative node IDs. Comparison
//! follows their e-class IDs, so choosing another node of the same class changes
//! nothing. Empty classes and duplicate node rows remain present.
//!
//! Each class's live slots occupy indices `0..class.slots`. Additional names in a
//! node's arguments receive indices after that range, local to that node and in
//! first-occurrence order. Thus equal private names in two different nodes do not
//! link their scopes. A child edge's `slots[k]` is the image of child live slot k
//! in the parent node's frame. Full symmetry groups are sorted so witnesses can
//! identify group elements by index.

use std::collections::{BTreeMap, BTreeSet};

use egraph_serialize::{ClassId, EGraph, NodeId};
use serde::{Deserialize, Serialize};

use crate::Error;

/// An [`EGraph`] document with an optional `slotted` field.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct AnnotatedEGraph {
    #[serde(flatten)]
    pub egraph: EGraph,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub slotted: Option<Slotted>,
}

/// Complete annotations: when present, every class and node must have an entry.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Slotted {
    pub classes: BTreeMap<ClassId, ClassSlots>,
    pub nodes: BTreeMap<NodeId, NodeSlots>,
}

/// Live slot names and their complete symmetry group, including identity.
/// Each element is a permutation mapping source slot indices to target indices.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ClassSlots {
    pub slots: Vec<String>,
    pub group: Vec<Vec<usize>>,
}

/// Arguments interleave direct slots and the standard node's ordered children.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeSlots {
    pub arguments: Vec<Argument>,
}

/// A direct slot or child invocation. Slots absent from the parent class are
/// private to this node.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Argument {
    Slot {
        slot: String,
    },
    /// Maps every live slot of the next [`egraph_serialize::Node::children`]
    /// entry's class injectively into the parent node's slot frame.
    Child {
        renaming: Vec<(String, String)>,
    },
}

/// A validated graph. Conversion rejects incomplete annotations, invalid edge
/// maps, and symmetry sets missing identity or closure. The exporter must supply
/// the full symmetry group: a valid proper subgroup cannot be detected here.
#[derive(Clone, Debug)]
pub struct Graph {
    pub(crate) classes: Vec<Class>,
    pub(crate) indices: BTreeMap<ClassId, usize>,
    pub(crate) roots: Vec<usize>,
}

impl Graph {
    /// Class and node counts after validation, retaining empty classes and duplicates.
    pub fn counts(&self) -> (usize, usize) {
        (
            self.classes.len(),
            self.classes.iter().map(|c| c.nodes.len()).sum(),
        )
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Class {
    pub id: ClassId,
    pub sort: Option<String>,
    pub slots: usize,
    pub group: Vec<Vec<usize>>,
    pub nodes: Vec<Node>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Label {
    pub op: String,
    pub subsumed: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct Node {
    pub id: NodeId,
    pub label: Label,
    pub args: Vec<Arg>,
    /// Number of private (binder or redundant) slots, in first-occurrence order.
    pub locals: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Arg {
    Slot(usize),
    Child { class: usize, slots: Vec<usize> },
}

impl Node {
    pub fn children(&self) -> impl Iterator<Item = usize> + '_ {
        self.args.iter().filter_map(|arg| match arg {
            Arg::Child { class, .. } => Some(*class),
            Arg::Slot(_) => None,
        })
    }
}

/// Whether the supplied permutations form a group, including identity.
/// Each input must already be a permutation of `0..degree`.
pub(crate) fn closed_group(group: &BTreeSet<Vec<usize>>, degree: usize) -> bool {
    let identity: Vec<_> = (0..degree).collect();
    if !group.contains(&identity) {
        return false;
    }
    let mut generated = BTreeSet::from([identity.clone()]);
    let mut generators = Vec::new();
    for p in group {
        if generated.contains(p) {
            continue;
        }
        // Add a generator only when the previous ones cannot produce it. Close
        // the generated set under these generators, rejecting any product absent
        // from the supplied group. This validates closure without repairing input.
        generators.push(p);
        let mut pending: Vec<_> = generated.iter().cloned().collect();
        let mut i = 0;
        while i < pending.len() {
            for generator in &generators {
                let product: Vec<_> = pending[i].iter().map(|&v| generator[v]).collect();
                if !group.contains(&product) {
                    return false;
                }
                if generated.insert(product.clone()) {
                    pending.push(product);
                }
            }
            i += 1;
        }
    }
    true
}

pub(crate) fn bijection(values: &[usize], degree: usize) -> bool {
    values.len() == degree
        && values.iter().copied().collect::<BTreeSet<_>>() == (0..degree).collect()
}

impl TryFrom<&AnnotatedEGraph> for Graph {
    type Error = Error;

    fn try_from(doc: &AnnotatedEGraph) -> Result<Self, Error> {
        let graph = &doc.egraph;
        let mut ids: BTreeSet<_> = graph.class_data.keys().cloned().collect();
        ids.extend(graph.nodes.values().map(|n| n.eclass.clone()));
        if let Some(slotted) = &doc.slotted {
            // An explicitly annotated empty class must not disappear.
            ids.extend(slotted.classes.keys().cloned());
            if ids != slotted.classes.keys().cloned().collect()
                || graph.nodes.keys().cloned().collect::<BTreeSet<_>>()
                    != slotted.nodes.keys().cloned().collect()
            {
                return Err(Error(
                    "slotted annotations must cover exactly the graph's classes and nodes".into(),
                ));
            }
        }
        let indices: BTreeMap<_, _> = ids.into_iter().enumerate().map(|(i, id)| (id, i)).collect();
        let mut classes = Vec::new();
        let mut named_slots = Vec::new();
        for id in indices.keys() {
            let (slots, group) = if let Some(slotted) = &doc.slotted {
                let data = &slotted.classes[id];
                let slots: BTreeMap<_, _> = data
                    .slots
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(i, s)| (s, i))
                    .collect();
                if slots.len() != data.slots.len() {
                    return Err(Error(format!("{id}: repeated class slot")));
                }
                let group: BTreeSet<_> = data.group.iter().cloned().collect();
                if group.len() != data.group.len()
                    || group.iter().any(|p| !bijection(p, slots.len()))
                    || !closed_group(&group, slots.len())
                {
                    return Err(Error(format!("{id}: invalid or incomplete symmetry group")));
                }
                (slots, group.into_iter().collect())
            } else {
                (BTreeMap::new(), vec![vec![]])
            };
            classes.push(Class {
                id: id.clone(),
                sort: graph.class_data.get(id).and_then(|c| c.typ.clone()),
                slots: slots.len(),
                group,
                nodes: Vec::new(),
            });
            named_slots.push(slots);
        }
        let mut node_ids: Vec<_> = graph.nodes.keys().collect();
        node_ids.sort();
        for id in node_ids {
            let raw = &graph.nodes[id];
            let class = indices[&raw.eclass];
            let mut frame = named_slots[class].clone();
            let mut args = Vec::new();
            let mut children = raw.children.iter();
            let ordinary: Vec<_>;
            let annotations = if let Some(slotted) = &doc.slotted {
                &slotted.nodes[id].arguments
            } else {
                ordinary = raw
                    .children
                    .iter()
                    .map(|_| Argument::Child { renaming: vec![] })
                    .collect();
                &ordinary
            };
            for arg in annotations {
                match arg {
                    Argument::Slot { slot } => {
                        let fresh = frame.len();
                        args.push(Arg::Slot(*frame.entry(slot.clone()).or_insert(fresh)));
                    }
                    Argument::Child { renaming } => {
                        let child_id = children.next().ok_or_else(|| {
                            Error(format!("{id}: too many annotated child edges"))
                        })?;
                        let child = graph
                            .nodes
                            .get(child_id)
                            .ok_or_else(|| Error(format!("{id}: missing child node {child_id}")))?;
                        let child_class = indices[&child.eclass];
                        let domain = &named_slots[child_class];
                        let keys: BTreeSet<_> = renaming.iter().map(|(k, _)| k).collect();
                        let values: BTreeSet<_> = renaming.iter().map(|(_, v)| v).collect();
                        if keys.len() != renaming.len()
                            || values.len() != renaming.len()
                            || keys != domain.keys().collect()
                        {
                            return Err(Error(format!(
                                "{id}: child slot map must be injective with exactly the child's slots as its domain"
                            )));
                        }
                        let mut slots = vec![0; domain.len()];
                        for (key, value) in renaming {
                            let fresh = frame.len();
                            slots[domain[key]] = *frame.entry(value.clone()).or_insert(fresh);
                        }
                        args.push(Arg::Child {
                            class: child_class,
                            slots,
                        });
                    }
                }
            }
            if children.next().is_some() {
                return Err(Error(format!("{id}: missing annotated child edges")));
            }
            classes[class].nodes.push(Node {
                id: id.clone(),
                label: Label {
                    op: raw.op.clone(),
                    subsumed: raw.subsumed,
                },
                args,
                locals: frame.len() - named_slots[class].len(),
            });
        }
        let roots = graph
            .root_eclasses
            .iter()
            .map(|id| {
                indices
                    .get(id)
                    .copied()
                    .ok_or_else(|| Error(format!("missing root class {id}")))
            })
            .collect::<Result<_, _>>()?;
        Ok(Self {
            classes,
            indices,
            roots,
        })
    }
}

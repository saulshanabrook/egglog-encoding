//! Check a supplied correspondence without searching for replacements.
//!
//! A witness fixes the class and live-slot bijections, each node's target and
//! private-slot bijection, and its parent/child symmetry choices. Verification
//! checks these choices directly, without colors or search's node matcher. Every
//! class and node must be covered exactly once, and live-slot maps must conjugate
//! the complete groups. Thus a duplicate or omitted node cannot be hidden by reuse.

use std::collections::{BTreeMap, BTreeSet};

use egraph_serialize::{ClassId, NodeId};
use serde::{Deserialize, Serialize};

use crate::Error;
use crate::graph::{Arg, Graph, bijection};

/// Explicit choices sufficient to check an isomorphism without any search.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Witness {
    /// One correspondence for every source class, keyed by its serialized ID.
    pub classes: BTreeMap<ClassId, ClassMatch>,
}

/// A class correspondence, with a shared live-slot map and a bijection on its nodes.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ClassMatch {
    pub target: ClassId,
    /// Target slot index for each source class slot.
    pub slots: Vec<usize>,
    /// One correspondence for every source node in this class, keyed by its ID.
    pub nodes: BTreeMap<NodeId, NodeMatch>,
}

/// A node correspondence and the local choices needed to compare its arguments.
/// These choices are independent of the choices for other nodes in the same class.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeMatch {
    pub target: NodeId,
    /// Target private-slot index for each source private slot. Both use zero-based
    /// first-occurrence order across arguments and child renamings.
    pub locals: Vec<usize>,
    /// Index into the target class's lexicographically sorted symmetry group.
    pub parent: usize,
    /// Target child's sorted-group index per child occurrence, in argument order.
    pub children: Vec<usize>,
}

/// Check the witness's class, slot, group, root, and node correspondences.
/// Returns an error if any obligation fails.
pub fn verify(left: &Graph, right: &Graph, witness: &Witness) -> Result<(), Error> {
    let invalid = |reason: &str| Error(format!("invalid witness: {reason}"));
    if witness.classes.keys().collect::<BTreeSet<_>>() != left.indices.keys().collect()
        || witness
            .classes
            .values()
            .map(|c| &c.target)
            .collect::<BTreeSet<_>>()
            != right.indices.keys().collect()
        || left.classes.len() != right.classes.len()
    {
        return Err(invalid("not a bijection on classes"));
    }
    let phi: Vec<_> = left
        .classes
        .iter()
        .map(|c| right.indices[&witness.classes[&c.id].target])
        .collect();
    if left.roots.iter().map(|&c| phi[c]).collect::<Vec<_>>() != right.roots {
        return Err(invalid("root classes do not correspond"));
    }
    for (a, source) in left.classes.iter().enumerate() {
        let target = &right.classes[phi[a]];
        let class = &witness.classes[&source.id];
        if source.sort != target.sort {
            return Err(invalid("class sorts differ"));
        }
        if source.slots != target.slots || !bijection(&class.slots, target.slots) {
            return Err(invalid("slot map is not a bijection"));
        }
        if source.group.len() != target.group.len() {
            return Err(invalid("symmetry group sizes differ"));
        }
        for p in &source.group {
            let mut transported = vec![0; target.slots];
            for (i, &j) in p.iter().enumerate() {
                transported[class.slots[i]] = class.slots[j];
            }
            if target.group.binary_search(&transported).is_err() {
                return Err(invalid("slot map does not conjugate the symmetry groups"));
            }
        }
        if class.nodes.keys().collect::<BTreeSet<_>>()
            != source.nodes.iter().map(|n| &n.id).collect()
            || class
                .nodes
                .values()
                .map(|n| &n.target)
                .collect::<BTreeSet<_>>()
                != target.nodes.iter().map(|n| &n.id).collect()
            || source.nodes.len() != target.nodes.len()
        {
            return Err(invalid("not a bijection on nodes"));
        }
        let targets: BTreeMap<_, _> = target.nodes.iter().map(|n| (&n.id, n)).collect();
        for node in &source.nodes {
            let choice = &class.nodes[&node.id];
            let other = targets[&choice.target];
            if node.label != other.label || node.args.len() != other.args.len() {
                return Err(invalid("node labels or arities differ"));
            }
            if node.locals != other.locals || !bijection(&choice.locals, other.locals) {
                return Err(invalid("private slot map is not a bijection"));
            }
            let parent = target
                .group
                .get(choice.parent)
                .ok_or_else(|| invalid("parent symmetry index out of bounds"))?;
            let source_slot = |s: usize| {
                if s < source.slots {
                    class.slots[s]
                } else {
                    target.slots + choice.locals[s - source.slots]
                }
            };
            let target_slot = |s: usize| if s < target.slots { parent[s] } else { s };
            let mut children = choice.children.iter();
            for (arg, other_arg) in node.args.iter().zip(&other.args) {
                match (arg, other_arg) {
                    (Arg::Slot(s), Arg::Slot(t)) if source_slot(*s) == target_slot(*t) => {}
                    (
                        Arg::Child {
                            class: child,
                            slots,
                        },
                        Arg::Child {
                            class: other_child,
                            slots: other_slots,
                        },
                    ) => {
                        if phi[*child] != *other_child {
                            return Err(invalid("child classes differ"));
                        }
                        let index = children
                            .next()
                            .ok_or_else(|| invalid("missing child symmetry"))?;
                        let symmetry = right.classes[*other_child]
                            .group
                            .get(*index)
                            .ok_or_else(|| invalid("child symmetry index out of bounds"))?;
                        let child_map = &witness.classes[&left.classes[*child].id].slots;
                        // Let A, B be the source/target edge maps, S the source
                        // parent's live/private slot map, T the child's live-slot
                        // map, and p, h the chosen target parent/child symmetries.
                        // For every source child slot s, check:
                        //     S(A(s)) = p(B(h(T(s))))
                        // Here p fixes private slots. This checks the commuting
                        // maps directly, independently of search's node matcher.
                        for (slot, &image) in slots.iter().enumerate() {
                            let mapped = *child_map
                                .get(slot)
                                .ok_or_else(|| invalid("missing child slot"))?;
                            let target_key = *symmetry
                                .get(mapped)
                                .ok_or_else(|| invalid("invalid child slot map"))?;
                            if source_slot(image) != target_slot(other_slots[target_key]) {
                                return Err(invalid("child slot maps differ"));
                            }
                        }
                    }
                    _ => return Err(invalid("direct slot or argument kind differs")),
                }
            }
            if children.next().is_some() {
                return Err(invalid("extra child symmetries"));
            }
        }
    }
    Ok(())
}

//! Slot renaming, shape, and total-mapping algorithms.

use super::Renaming;
use egglog::sort::find_mapping;
use std::collections::{BTreeMap, BTreeSet};

/// A node's canonical edges, renaming back to its frame, and self-symmetries.
#[derive(Debug)]
pub(crate) struct NodeShape {
    pub edges: Vec<Renaming>,
    pub back: Renaming,
    pub symmetries: Vec<Renaming>,
}

impl NodeShape {
    pub fn into_maps(self) -> impl Iterator<Item = Renaming> {
        self.edges
            .into_iter()
            .chain([self.back])
            .chain(self.symmetries)
    }
}

/// The canonical spelling of a node's edges: its slots renumbered `0, 1, 2…` in order
/// of first occurrence, scanning the edges in order and each edge by child slot.
/// Records the renumbered edges and the renaming back to the node's own names. Two nodes are equal up to a renaming of their slots exactly when their
/// shapes agree.
pub(crate) fn shape(edges: &[Renaming]) -> NodeShape {
    let mut number: BTreeMap<i64, i64> = BTreeMap::new();
    let mut out: Vec<Renaming> = Vec::with_capacity(edges.len() + 1);
    for edge in edges {
        let mut spelled = Renaming::new();
        for (&child_slot, &node_slot) in edge {
            let next = number.len() as i64;
            spelled.insert(child_slot, *number.entry(node_slot).or_insert(next));
        }
        out.push(spelled);
    }
    NodeShape {
        edges: out,
        back: number.into_iter().map(|(slot, n)| (n, slot)).collect(),
        symmetries: Vec::new(),
    }
}

/// A node's least spelling under its children's symmetries, the renaming back to
/// its frame, and its non-identity self-symmetries. Nodes equal under their
/// children's symmetries have equal canonical edges. Group elements that do not
/// permute the corresponding child's slots are ignored.
pub(crate) fn node_shape(edges: &[Renaming], groups: &[Vec<Renaming>]) -> NodeShape {
    node_shape_impl(edges, groups, |_, _| (), |_, _| {}, |_, _| {})
}

/// Report the child readings selected for each new minimum and self-symmetry.
pub(crate) fn node_shape_with(
    edges: &[Renaming],
    groups: &[Vec<Renaming>],
    minimum: impl FnMut(&NodeShape, &[Renaming]),
    symmetry: impl FnMut(&Renaming, &[Renaming]),
) -> NodeShape {
    node_shape_impl(edges, groups, selected_reading, minimum, symmetry)
}

fn selected_reading(edge: &Renaming, group: Option<&Renaming>) -> Renaming {
    group
        .cloned()
        .unwrap_or_else(|| edge.keys().map(|s| (*s, *s)).collect())
}

// Ordinary execution uses zero-sized readings, so only proof replay allocates
// and clones the selected group elements. Both follow the same enumeration.
fn node_shape_impl<T: Clone + Ord>(
    edges: &[Renaming],
    groups: &[Vec<Renaming>],
    selected: impl Fn(&Renaming, Option<&Renaming>) -> T,
    mut minimum: impl FnMut(&NodeShape, &[T]),
    mut symmetry: impl FnMut(&Renaming, &[T]),
) -> NodeShape {
    let own = shape(edges);
    let mut best: Option<NodeShape> = None;
    let mut symmetries: Vec<Renaming> = Vec::new();
    for (variant, chosen) in readings(edges, groups, selected) {
        let spelled = shape(&variant);
        if spelled.edges == own.edges {
            // variant = b . canonical and the node = own_back . canonical, so
            // b . own_back^-1 renames the node's slots onto themselves
            let element: Renaming = own
                .back
                .iter()
                .filter_map(|(n, &slot)| spelled.back.get(n).map(|&image| (slot, image)))
                .collect();
            if element.iter().any(|(from, to)| from != to) {
                symmetry(&element, &chosen);
                symmetries.push(element);
            }
        }
        if best.as_ref().is_none_or(|b| spelled.edges < b.edges) {
            minimum(&spelled, &chosen);
            best = Some(spelled);
        }
    }
    symmetries.sort();
    symmetries.dedup();
    let mut out = best.unwrap_or(own);
    out.symmetries = symmetries;
    out
}

/// Each column's edge under its child's symmetries, with the chosen group elements.
/// Only symmetries that permute the column's slots participate. Readings are sorted
/// within each column; the first column varies fastest. This order breaks ties in
/// [`node_shape`] when several readings have the same canonical shape.
fn readings<T: Clone + Ord>(
    edges: &[Renaming],
    groups: &[Vec<Renaming>],
    selected: impl Fn(&Renaming, Option<&Renaming>) -> T,
) -> impl Iterator<Item = (Vec<Renaming>, Vec<T>)> {
    let columns: Vec<Vec<(Renaming, T)>> = edges
        .iter()
        .enumerate()
        .map(|(i, edge)| {
            let domain: BTreeSet<i64> = edge.keys().copied().collect();
            let mut out = vec![(edge.clone(), selected(edge, None))];
            for g in groups.get(i).map(Vec::as_slice).unwrap_or_default() {
                if g.keys().copied().collect::<BTreeSet<_>>() == domain
                    && g.values().copied().collect::<BTreeSet<_>>() == domain
                {
                    out.push((
                        g.iter().map(|(&s, &t)| (s, edge[&t])).collect(),
                        selected(edge, Some(g)),
                    ));
                }
            }
            out.sort();
            out.dedup_by(|a, b| a.0 == b.0);
            out
        })
        .collect();
    let total: usize = columns.iter().map(Vec::len).product();
    (0..total).map(move |mut n| {
        let mut variant = Vec::with_capacity(columns.len());
        let mut chosen = Vec::with_capacity(columns.len());
        for column in &columns {
            let (read, g) = &column[n % column.len()];
            variant.push(read.clone());
            chosen.push(g.clone());
            n /= column.len();
        }
        (variant, chosen)
    })
}

/// [`find_mapping`] extended to be *total* on a domain, minting a
/// fresh slot for every domain key the constraints leave unnamed.
///
/// Arguments come flat as `[avoid, domain, first..., second...]`. The
/// constraint part is solved exactly as in [`find_mapping`]; each
/// remaining key of `domain` is then named with the *smallest* non-negative
/// value not already spoken for, which keeps the result injective and disjoint
/// from `avoid`.
///
/// `None` on the same conditions as [`find_mapping`], or on fewer than
/// two leading maps.
pub(super) fn find_mapping_total(maps: &[Renaming]) -> Option<Renaming> {
    let (head, pairs) = maps.split_at_checked(2)?;
    let (avoid, domain) = (&head[0], &head[1]);

    let mut mapping = find_mapping(pairs)?;

    let mut used: BTreeSet<i64> = mapping
        .values()
        .chain(avoid.keys())
        .chain(avoid.values())
        .copied()
        .collect();

    let mut next = 0;
    for k in domain.keys() {
        if mapping.contains_key(k) {
            continue;
        }
        while used.contains(&next) {
            next += 1;
        }
        used.insert(next);
        mapping.insert(*k, next);
    }
    Some(Renaming(mapping))
}

#[cfg(test)]
mod shape_tests {
    use super::Renaming;
    use super::shape;

    fn m(pairs: &[(i64, i64)]) -> Renaming {
        pairs.iter().copied().collect()
    }

    #[test]
    fn renamed_nodes_share_a_shape_and_back_undoes_it() {
        let a = shape(&[m(&[(0, 5)]), m(&[(0, 3)])]);
        let b = shape(&[m(&[(0, 1)]), m(&[(0, 2)])]);
        assert_eq!(a.edges, b.edges);
        assert_eq!(a.edges[0], m(&[(0, 0)]));
        assert_eq!(a.edges[1], m(&[(0, 1)]));
        assert_eq!(a.back, m(&[(0, 5), (1, 3)]));
        assert_eq!(b.back, m(&[(0, 1), (1, 2)]));
    }

    #[test]
    fn a_shared_slot_is_a_different_node() {
        let same = shape(&[m(&[(0, 5)]), m(&[(0, 5)])]);
        let apart = shape(&[m(&[(0, 5)]), m(&[(0, 3)])]);
        assert_eq!(same.edges[1], m(&[(0, 0)]));
        assert_ne!(same.edges, apart.edges);
    }

    #[test]
    fn private_slots_of_one_column_may_be_permuted() {
        let xy = shape(&[m(&[(0, 0), (1, 1)]), m(&[(0, 2), (1, 3)])]);
        let yx = shape(&[m(&[(0, 0), (1, 1)]), m(&[(0, 3), (1, 2)])]);
        assert_eq!(xy.edges, yx.edges);
        let shared_xy = shape(&[m(&[(0, 0)]), m(&[(0, 0), (1, 1)])]);
        let shared_yx = shape(&[m(&[(0, 0)]), m(&[(0, 1), (1, 0)])]);
        assert_ne!(shared_xy.edges, shared_yx.edges);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tied_shapes_retain_the_selected_reading_and_back_map() {
        // Both readings give the same canonical unary node. The chosen back
        // map matters when a parent binds only one of this child's two slots.
        let swapped = Renaming::from([(0, 1), (1, 0)]);
        let identity = Renaming::from([(0, 0), (1, 1)]);
        let edges = [swapped.clone()];
        let groups = [vec![identity.clone(), swapped.clone()]];
        let variants: Vec<_> = readings(&edges, &groups, selected_reading).collect();
        assert_eq!(variants[0], (vec![identity.clone()], vec![swapped]));
        assert_eq!(shape(&variants[0].0).edges, shape(&variants[1].0).edges);
        assert_eq!(node_shape(&edges, &groups).back, identity);
    }

    #[test]
    fn proof_tracing_preserves_canonical_shapes_and_symmetries() {
        let identity = Renaming::from([(0, 0), (1, 1)]);
        let swapped = Renaming::from([(0, 1), (1, 0)]);
        let shifted = Renaming::from([(0, 4), (1, 7)]);
        let restricted = Renaming::from([(0, 0)]);
        let groups = vec![identity.clone(), swapped.clone(), restricted.clone()];
        for left in [&identity, &swapped, &shifted, &restricted] {
            for right in [&identity, &swapped, &shifted, &restricted] {
                let edges = [left.clone(), right.clone()];
                for groups in [vec![], vec![groups.clone()], vec![groups.clone(); 2]] {
                    let ordinary: Vec<_> = node_shape(&edges, &groups).into_maps().collect();
                    let traced: Vec<_> = node_shape_with(&edges, &groups, |_, _| {}, |_, _| {})
                        .into_maps()
                        .collect();
                    assert_eq!(ordinary, traced);
                }
            }
        }
    }
}

//! Slot renaming, shape, and total-mapping algorithms.

use super::Renaming;
use crate::sort::map::find_mapping;
use std::collections::{BTreeMap, BTreeSet};

/// Internal result of canonicalizing a node. Only the primitive boundary flattens
/// this into the legacy vector representation.
#[derive(Debug)]
pub(super) struct NodeShape {
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
pub(super) fn shape(edges: &[Renaming]) -> NodeShape {
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

/// A node's canonical spelling and the symmetries it gives its class, from one walk of
/// the readings its children's symmetries allow.
///
/// Records canonical edges, the renaming back to the node's own names, and its
/// non-identity symmetries. A reading composes each column's edge
/// with a symmetry of that column's class; only a renaming that permutes the column's
/// own slots is one, so a stale symmetry is ignored. The least reading is the spelling
/// every reading agrees on, so two nodes equal up to their children's symmetries have
/// equal canonical edges. A reading that spells the node the way it already spells
/// itself says the class equals itself under the renaming between them, which is the
/// reference's `weak_shape` over `get_group_compatible_variants` and its
/// `determine_self_symmetries` in one pass.
pub(super) fn node_shape(edges: &[Renaming], groups: &[Vec<Renaming>]) -> NodeShape {
    let own = shape(edges);
    let mut best: Option<NodeShape> = None;
    let mut symmetries: Vec<Renaming> = Vec::new();
    for variant in readings(edges, groups) {
        let spelled = shape(&variant);
        if spelled.edges == own.edges {
            // variant = b . canonical and the node = own_back . canonical, so
            // b . own_back^-1 renames the node's slots onto themselves
            let symmetry: Renaming = own
                .back
                .iter()
                .filter_map(|(n, &slot)| spelled.back.get(n).map(|&image| (slot, image)))
                .collect();
            if symmetry.iter().any(|(from, to)| from != to) {
                symmetries.push(symmetry);
            }
        }
        if best.as_ref().is_none_or(|b| spelled.edges < b.edges) {
            best = Some(spelled);
        }
    }
    symmetries.sort();
    symmetries.dedup();
    let mut out = best.unwrap_or(own);
    out.symmetries = symmetries;
    out
}

/// Each column's edge, and the edge through every symmetry of its child's class: the
/// readings of a node that spell the same invocation. A renaming that does not permute
/// the column's own slots is not one of them, so a stale symmetry is ignored.
fn readings(edges: &[Renaming], groups: &[Vec<Renaming>]) -> impl Iterator<Item = Vec<Renaming>> {
    let columns: Vec<Vec<Renaming>> = edges
        .iter()
        .enumerate()
        .map(|(i, edge)| {
            let domain: BTreeSet<i64> = edge.keys().copied().collect();
            let mut out = vec![edge.clone()];
            for g in groups.get(i).map(Vec::as_slice).unwrap_or_default() {
                if g.keys().copied().collect::<BTreeSet<_>>() == domain
                    && g.values().copied().collect::<BTreeSet<_>>() == domain
                {
                    out.push(g.iter().map(|(&s, &t)| (s, edge[&t])).collect());
                }
            }
            out.sort();
            out.dedup();
            out
        })
        .collect();
    let total: usize = columns.iter().map(Vec::len).product();
    (0..total).map(move |mut n| {
        let mut variant = Vec::with_capacity(columns.len());
        for column in &columns {
            variant.push(column[n % column.len()].clone());
            n /= column.len();
        }
        variant
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

//! Finite symmetry-group operations, independent of egglog's value registry.
use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet};

type Map<T> = BTreeMap<T, T>;

use crate::sort::map::compose;

pub(super) fn restrict<T: Copy + Ord>(
    group: &[impl Borrow<Map<T>>],
    slots: &Map<T>,
) -> Vec<Map<T>> {
    group
        .iter()
        .map(|g| compose(slots, &compose(g.borrow(), slots)))
        .collect()
}

/// Close a set of finite permutations under composition.
pub(super) fn close<T: Copy + Ord>(group: &[impl Borrow<Map<T>>]) -> Vec<Map<T>> {
    let mut known: Vec<Map<T>> = group.iter().map(|g| g.borrow().clone()).collect();
    let mut seen: BTreeSet<Map<T>> = known.iter().cloned().collect();
    let mut frontier: Vec<usize> = (0..known.len()).collect();
    while !frontier.is_empty() {
        let mut fresh = Vec::new();
        for &i in &frontier {
            for j in 0..known.len() {
                for m in [compose(&known[i], &known[j]), compose(&known[j], &known[i])] {
                    if seen.insert(m.clone()) {
                        fresh.push(m);
                    }
                }
            }
        }
        let start = known.len();
        known.extend(fresh);
        frontier = (start..known.len()).collect();
    }
    known
}

/// Least representative for each inverse action on the pinned slots. A reading
/// maps a nested node's slots into its parent's frame, so the parent pins images,
/// not inputs, of that permutation. The indices retain the caller's already
/// interned values; ordering is by actual slot numbers.
pub(super) fn coset_reps<T: Copy + Ord>(
    group: &[impl Borrow<Map<T>>],
    pinned: &Map<T>,
) -> Vec<usize> {
    let mut least: BTreeMap<Map<T>, usize> = BTreeMap::new();
    for (i, g) in group.iter().enumerate() {
        let g = g.borrow();
        let key = g
            .iter()
            .filter(|(_, v)| pinned.contains_key(v))
            .map(|(k, v)| (*v, *k))
            .collect();
        match least.get(&key) {
            Some(&j) if group[j].borrow() <= g => {}
            _ => {
                least.insert(key, i);
            }
        }
    }
    least.into_values().collect()
}

pub(super) fn coset_min<T: Copy + Ord>(
    map: &Map<T>,
    group: &[impl Borrow<Map<T>>],
) -> Option<Map<T>> {
    group.iter().map(|g| compose(map, g.borrow())).min()
}

pub(super) fn coset_same<T: Copy + Ord>(
    a: &Map<T>,
    b: &Map<T>,
    group: &[impl Borrow<Map<T>>],
) -> bool {
    group.iter().any(|g| compose(b, g.borrow()) == *a)
}

pub(super) fn slot_closure<T: Copy + Ord>(group: &[impl Borrow<Map<T>>], slots: &Map<T>) -> Map<T> {
    let mut kept: BTreeSet<T> = slots.keys().copied().collect();
    for g in group {
        let g = g.borrow();
        let forward: BTreeSet<T> = compose(g, slots).values().copied().collect();
        let inverse: Map<T> = g.iter().map(|(k, v)| (*v, *k)).collect();
        let backward: BTreeSet<T> = compose(&inverse, slots).values().copied().collect();
        kept.retain(|x| forward.contains(x) && backward.contains(x));
    }
    kept.into_iter().map(|x| (x, x)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closure_generates_identity_and_inverse() {
        let cycle = Map::from([(0, 1), (1, 2), (2, 0)]);
        let group = close(std::slice::from_ref(&cycle));
        assert_eq!(group.len(), 3);
        assert!(group.contains(&Map::from([(0, 0), (1, 1), (2, 2)])));
        assert!(group.contains(&Map::from([(0, 2), (1, 0), (2, 1)])));
        assert_eq!(close(&group).len(), 3);
        assert!(coset_same(&cycle, &group[1], &group));
        assert_eq!(coset_min(&cycle, &group), group.iter().min().cloned());
    }

    #[test]
    fn cosets_distinguish_only_the_pinned_action() {
        let id = Map::from([(0, 0), (1, 1), (2, 2)]);
        let swap = Map::from([(0, 0), (1, 2), (2, 1)]);
        let group = vec![swap, id.clone()];
        assert_eq!(coset_reps(&group, &Map::from([(0, 0)])), vec![1]);
        assert_eq!(coset_reps(&group, &Map::from([(1, 1)])).len(), 2);
        let slots = Map::from([(0, 0), (1, 1)]);
        assert_eq!(slot_closure(&group, &slots), Map::from([(0, 0)]));
        assert_eq!(restrict(&group, &slots), vec![Map::from([(0, 0)]), slots]);
    }

    #[test]
    fn readings_cover_every_preimage_of_a_pinned_slot() {
        let group = close(&[
            Map::from([(0, 1), (1, 0), (2, 2)]),
            Map::from([(0, 1), (1, 2), (2, 0)]),
        ]);
        assert_eq!(group.len(), 6);
        // For S3, grouping by g(0) selects two readings with the same g^-1(0)
        // and loses the match that puts the third node slot at the parent's 0.
        for pinned in 0..3 {
            let reps = coset_reps(&group, &Map::from([(pinned, pinned)]));
            assert_eq!(reps.len(), 3);
            let preimages: BTreeSet<_> = reps
                .iter()
                .map(|&i| *group[i].iter().find(|(_, v)| **v == pinned).unwrap().0)
                .collect();
            assert_eq!(preimages, BTreeSet::from([0, 1, 2]));
        }
    }
}

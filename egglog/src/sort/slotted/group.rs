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

/// Close finite slot maps under composition, including partial maps during restriction.
pub(super) fn close<T: Copy + Ord>(group: &[impl Borrow<Map<T>>]) -> Vec<Map<T>> {
    let mut known = Vec::new();
    let mut seen = BTreeSet::new();
    let mut generators = Vec::new();
    for generator in group {
        let generator = generator.borrow();
        if !seen.insert(generator.clone()) {
            continue;
        }
        generators.push(generator);
        known.push(generator.clone());
        // Every generated map is a nonempty word in the generators. Extending
        // words on one side suffices, including for partial maps during slot
        // restriction. Revisit old words when adding a new generator; any input
        // already generated can be skipped. In particular, an already closed
        // group needs only a small generating subset, not all pairs of elements.
        let mut next = 0;
        while next < known.len() {
            for generator in &generators {
                let m = compose(&known[next], generator);
                if seen.insert(m.clone()) {
                    known.push(m);
                }
            }
            next += 1;
        }
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
    fn closure_preserves_all_products_of_partial_bijections() {
        // Restriction can temporarily produce partial maps. Check every subset
        // of the seven partial bijections on two slots against all-pairs closure.
        let maps = [
            Map::new(),
            Map::from([(0, 0)]),
            Map::from([(0, 1)]),
            Map::from([(1, 0)]),
            Map::from([(1, 1)]),
            Map::from([(0, 0), (1, 1)]),
            Map::from([(0, 1), (1, 0)]),
        ];
        for mask in 0..1 << maps.len() {
            let mut input: Vec<_> = maps
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, m)| m.clone())
                .collect();
            let mut expected: BTreeSet<_> = input.iter().cloned().collect();
            loop {
                let before = expected.clone();
                for a in &before {
                    for b in &before {
                        expected.insert(compose(a, b));
                    }
                }
                if expected == before {
                    break;
                }
            }
            assert_eq!(close(&input).into_iter().collect::<BTreeSet<_>>(), expected);
            input.reverse();
            input.extend(input.clone());
            assert_eq!(close(&input).into_iter().collect::<BTreeSet<_>>(), expected);
        }
    }

    #[test]
    fn closure_of_noncommuting_generators_and_their_full_group_agree() {
        let cycle = Map::from([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
        let swap = Map::from([(0, 1), (1, 0), (2, 2), (3, 3), (4, 4)]);
        let group: BTreeSet<_> = close(&[cycle, swap]).into_iter().collect();
        assert_eq!(group.len(), 120);
        let elements: Vec<_> = group.iter().rev().collect();
        assert_eq!(close(&elements).into_iter().collect::<BTreeSet<_>>(), group);
    }

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

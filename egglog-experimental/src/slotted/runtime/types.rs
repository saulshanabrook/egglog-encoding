//! Domain types used by matching and substitution. Egglog represents both kinds
//! of values as maps; the algorithms distinguish them here.
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;

/// A partial mapping of slot names. Keep the common small frame inline, sorted
/// by signed slot number. Missing entries remain undefined, never identity.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Renaming(smallvec::SmallVec<[(i64, i64); 4]>);

impl Renaming {
    pub(crate) fn new() -> Self {
        Self::default()
    }
    pub(crate) fn insert(&mut self, from: i64, to: i64) {
        match self.0.binary_search_by_key(&from, |(key, _)| *key) {
            Ok(i) => self.0[i].1 = to,
            Err(i) => self.0.insert(i, (from, to)),
        }
    }
    pub(crate) fn remove(&mut self, slot: &i64) {
        if let Ok(i) = self.0.binary_search_by_key(slot, |(key, _)| *key) {
            self.0.remove(i);
        }
    }
    pub(crate) fn retain(&mut self, mut f: impl FnMut(&i64, &mut i64) -> bool) {
        self.0.retain_mut(|(k, v)| f(k, v));
    }
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }
    pub(crate) fn get(&self, key: &i64) -> Option<&i64> {
        self.0
            .binary_search_by_key(key, |(key, _)| *key)
            .ok()
            .map(|i| &self.0[i].1)
    }
    pub(crate) fn contains_key(&self, key: &i64) -> bool {
        self.get(key).is_some()
    }
    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = (&i64, &i64)> + ExactSizeIterator {
        self.0.iter().map(|(k, v)| (k, v))
    }
    pub(crate) fn keys(&self) -> impl DoubleEndedIterator<Item = &i64> + ExactSizeIterator {
        self.0.iter().map(|(k, _)| k)
    }
    pub(crate) fn values(&self) -> impl DoubleEndedIterator<Item = &i64> + ExactSizeIterator {
        self.0.iter().map(|(_, v)| v)
    }
}

impl std::ops::Index<&i64> for Renaming {
    type Output = i64;
    fn index(&self, key: &i64) -> &i64 {
        self.get(key).expect("missing slot")
    }
}

impl FromIterator<(i64, i64)> for Renaming {
    fn from_iter<I: IntoIterator<Item = (i64, i64)>>(iter: I) -> Self {
        let mut out = Self::new();
        out.extend(iter);
        out
    }
}

impl<const N: usize> From<[(i64, i64); N]> for Renaming {
    fn from(entries: [(i64, i64); N]) -> Self {
        entries.into_iter().collect()
    }
}

impl From<BTreeMap<i64, i64>> for Renaming {
    fn from(entries: BTreeMap<i64, i64>) -> Self {
        Self(entries.into_iter().collect())
    }
}

impl Extend<(i64, i64)> for Renaming {
    fn extend<I: IntoIterator<Item = (i64, i64)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl IntoIterator for Renaming {
    type Item = (i64, i64);
    type IntoIter = smallvec::IntoIter<[(i64, i64); 4]>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Renaming {
    type Item = (&'a i64, &'a i64);
    type IntoIter =
        std::iter::Map<std::slice::Iter<'a, (i64, i64)>, fn(&'a (i64, i64)) -> Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|(k, v)| (k, v))
    }
}

// Keep the existing map-shaped JSON used in frame/binding proof terms.
impl Serialize for Renaming {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self.iter())
    }
}

impl<'de> Deserialize<'de> for Renaming {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        BTreeMap::<i64, i64>::deserialize(deserializer).map(Self::from)
    }
}

/// Public class slots, distinct from an edge's renaming of those slots.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SlotSet(BTreeSet<i64>);

impl SlotSet {
    pub(crate) fn from_identity(map: &Renaming) -> Option<Self> {
        map.iter()
            .all(|(a, b)| a == b)
            .then(|| map.keys().copied().collect())
    }
}

impl Deref for SlotSet {
    type Target = BTreeSet<i64>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl FromIterator<i64> for SlotSet {
    fn from_iter<I: IntoIterator<Item = i64>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compact_maps_preserve_order_domains_updates_and_proof_json() {
        // Cross the inline capacity, retain sparse/negative names, and update
        // duplicate keys. The old tree representation is the oracle.
        for count in 0..20 {
            let pairs = (0..count).rev().map(|i| (i * 7 - 50, 100 - i)).chain([
                (i64::MIN, i64::MAX),
                (-50, 17),
                (-50, -3),
            ]);
            let mut tree: BTreeMap<_, _> = pairs.clone().collect();
            let mut compact: Renaming = pairs.collect();
            assert!(compact.iter().eq(tree.iter()));
            assert_eq!(compact.get(&91), None);
            assert_eq!(compact.len(), tree.len());
            for key in [i64::MIN, -50, 91] {
                assert_eq!(compact.get(&key), tree.get(&key));
                compact.remove(&key);
                tree.remove(&key);
            }
            compact.retain(|k, v| {
                *v += 1;
                k % 2 == 0
            });
            tree.retain(|k, v| {
                *v += 1;
                k % 2 == 0
            });
            assert!(compact.iter().eq(tree.iter()));
            let text = serde_json::to_string(&compact).unwrap();
            assert_eq!(text, serde_json::to_string(&tree).unwrap());
            assert_eq!(serde_json::from_str::<Renaming>(&text).unwrap(), compact);
        }
    }
}

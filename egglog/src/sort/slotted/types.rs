//! Domain types used by matching and substitution. Egglog represents both kinds
//! of values as maps; the algorithms distinguish them here.
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;

/// A partial mapping of slot names. Edges decoded from external data must also
/// pass the caller's injectivity check; temporary mappings are built internally.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Renaming(pub(super) BTreeMap<i64, i64>);

impl Renaming {
    pub(super) fn new() -> Self {
        Self::default()
    }
    pub(super) fn insert(&mut self, from: i64, to: i64) {
        self.0.insert(from, to);
    }
    pub(super) fn remove(&mut self, slot: &i64) {
        self.0.remove(slot);
    }
    pub(super) fn retain(&mut self, f: impl FnMut(&i64, &mut i64) -> bool) {
        self.0.retain(f);
    }
}

impl Deref for Renaming {
    type Target = BTreeMap<i64, i64>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::borrow::Borrow<BTreeMap<i64, i64>> for Renaming {
    fn borrow(&self) -> &BTreeMap<i64, i64> {
        &self.0
    }
}

impl FromIterator<(i64, i64)> for Renaming {
    fn from_iter<I: IntoIterator<Item = (i64, i64)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<const N: usize> From<[(i64, i64); N]> for Renaming {
    fn from(entries: [(i64, i64); N]) -> Self {
        entries.into_iter().collect()
    }
}

impl Extend<(i64, i64)> for Renaming {
    fn extend<I: IntoIterator<Item = (i64, i64)>>(&mut self, iter: I) {
        self.0.extend(iter);
    }
}

impl IntoIterator for Renaming {
    type Item = (i64, i64);
    type IntoIter = std::collections::btree_map::IntoIter<i64, i64>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Renaming {
    type Item = (&'a i64, &'a i64);
    type IntoIter = std::collections::btree_map::Iter<'a, i64, i64>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// Public class slots, distinct from an edge's renaming of those slots.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SlotSet(BTreeSet<i64>);

impl SlotSet {
    pub(super) fn from_identity(map: &Renaming) -> Option<Self> {
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

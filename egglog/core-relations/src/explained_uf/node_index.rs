//! Sparse external IDs mapped to dense UF slots. Hot pages use direct slot
//! lookups; isolated IDs keep small sparse pages. No allocation follows the
//! largest global proof/term ID, and page storage stays bounded by live nodes.

use crate::{Value, common::HashMap, numeric_id::NumericId};

const PAGE_BITS: u32 = 10;
const PAGE_SIZE: usize = 1 << PAGE_BITS;
const DENSE_THRESHOLD: usize = 16;
const MISSING: u32 = u32::MAX;

#[derive(Clone)]
enum Page {
    Sparse(Vec<(u16, u32)>),
    Dense(Box<[u32; PAGE_SIZE]>),
}

#[derive(Clone, Default)]
pub(super) struct NodeIndex {
    pages: HashMap<u32, Page>,
}

impl NodeIndex {
    #[inline]
    pub(super) fn get(&self, value: Value) -> Option<usize> {
        let page = self.pages.get(&(value.rep() >> PAGE_BITS))?;
        let offset = (value.rep() as usize & (PAGE_SIZE - 1)) as u16;
        match page {
            Page::Sparse(entries) => entries
                .iter()
                .find(|(key, _)| *key == offset)
                .map(|(_, index)| *index as usize),
            Page::Dense(entries) => {
                let index = entries[offset as usize];
                (index != MISSING).then_some(index as usize)
            }
        }
    }

    pub(super) fn insert(&mut self, value: Value, index: usize) {
        let index: u32 = index.try_into().expect("UF slot exceeds Value domain");
        assert_ne!(index, MISSING);
        let page = self
            .pages
            .entry(value.rep() >> PAGE_BITS)
            .or_insert_with(|| Page::Sparse(Vec::new()));
        let offset = (value.rep() as usize & (PAGE_SIZE - 1)) as u16;
        match page {
            Page::Sparse(entries) => {
                entries.push((offset, index));
                if entries.len() == DENSE_THRESHOLD {
                    let mut dense = Box::new([MISSING; PAGE_SIZE]);
                    for &(key, index) in entries.iter() {
                        dense[key as usize] = index;
                    }
                    *page = Page::Dense(dense);
                }
            }
            Page::Dense(entries) => entries[offset as usize] = index,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sparse_ids_and_promoted_pages_preserve_missing_slots() {
        let mut map = NodeIndex::default();
        for (index, value) in (0..32)
            .map(|i| i * 2)
            .chain([1_000_000_000, u32::MAX - 1])
            .enumerate()
        {
            map.insert(Value::new(value), index);
            assert_eq!(map.get(Value::new(value)), Some(index));
        }
        assert_eq!(map.pages.len(), 3);
        assert!(matches!(map.pages[&0], Page::Dense(_)));
        for i in 0..32 {
            assert_eq!(map.get(Value::new(i * 2)), Some(i as usize));
            assert_eq!(map.get(Value::new(i * 2 + 1)), None);
        }
        assert_eq!(map.get(Value::new(u32::MAX)), None);
    }
}

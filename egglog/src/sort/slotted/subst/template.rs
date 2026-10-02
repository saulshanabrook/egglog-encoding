//! Shared spellings of extracted trees. Sharing saves storage; every child occurrence
//! still counts toward tree cost and gets fresh internal slots when compared.

use super::Slot;
use smallvec::SmallVec;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Name {
    Public(Slot),
    Inner(usize),
}

enum Part {
    Text(String),
    Slot(Name),
    Child {
        template: Arc<Template>,
        public: BTreeMap<Slot, Name>,
    },
}

#[derive(Default)]
pub(super) struct Template {
    parts: Vec<Part>,
    pub(super) public: BTreeSet<Slot>,
    inner_count: usize,
}

impl Template {
    pub(super) fn text(&mut self, text: impl Into<String>) {
        self.parts.push(Part::Text(text.into()));
    }

    pub(super) fn slot(&mut self, name: Name) {
        self.record_public(name);
        self.parts.push(Part::Slot(name));
    }

    fn record_public(&mut self, name: Name) {
        if let Name::Public(slot) = name {
            self.public.insert(slot);
        }
    }

    pub(super) fn fresh_inner(&mut self) -> Name {
        let name = Name::Inner(self.inner_count);
        self.inner_count = self
            .inner_count
            .checked_add(1)
            .expect("term has too many slots");
        name
    }

    pub(super) fn child(&mut self, template: Arc<Template>, public: BTreeMap<Slot, Name>) {
        for name in public.values() {
            self.record_public(*name);
        }
        self.parts.push(Part::Child { template, public });
    }

    /// The same UTF-8 byte ordering as comparing fully expanded canonical strings,
    /// stopping at the first difference and never allocating those strings.
    pub(super) fn compare(&self, other: &Self) -> Ordering {
        if std::ptr::eq(self, other) {
            Ordering::Equal
        } else {
            Spelling::new(self).cmp(Spelling::new(other))
        }
    }
}

/// An internal name belongs to an active occurrence on the traversal stack.
/// Descendants can refer to it through their public mappings, but it cannot
/// escape its owner. Popping the owner releases its entire local namespace.
#[derive(Clone, Copy)]
enum Resolved {
    Public(Slot),
    Inner { owner: usize, index: usize },
}

/// One occurrence of a shared template. Only this node's own internal slots
/// need storage; no flattened range is reserved for its descendants.
struct Walk<'a> {
    parts: std::slice::Iter<'a, Part>,
    public: BTreeMap<Slot, Resolved>,
    inner: Vec<Option<usize>>,
}

impl Walk<'_> {
    fn resolve(&self, name: Name, owner: usize) -> Resolved {
        match name {
            Name::Public(slot) => self.public[&slot],
            Name::Inner(index) => Resolved::Inner { owner, index },
        }
    }
}

struct Spelling<'a> {
    stack: Vec<Walk<'a>>,
    text: &'a [u8],
    // Digits in reverse order, then the p/i prefix, popped one byte at a time.
    number: SmallVec<[u8; 24]>,
    public: BTreeMap<Slot, usize>,
    next_inner: usize,
}

impl<'a> Spelling<'a> {
    fn new(template: &'a Template) -> Self {
        Self {
            stack: vec![Walk {
                parts: template.parts.iter(),
                public: template
                    .public
                    .iter()
                    .map(|s| (*s, Resolved::Public(*s)))
                    .collect(),
                inner: vec![None; template.inner_count],
            }],
            text: &[],
            number: SmallVec::new(),
            public: BTreeMap::new(),
            next_inner: 0,
        }
    }
}

impl Iterator for Spelling<'_> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        loop {
            if let Some((&byte, rest)) = self.text.split_first() {
                self.text = rest;
                return Some(byte);
            }
            if let Some(byte) = self.number.pop() {
                return Some(byte);
            }
            let owner = self.stack.len().checked_sub(1)?;
            let walk = &mut self.stack[owner];
            match walk.parts.next() {
                None => {
                    self.stack.pop();
                }
                Some(Part::Text(text)) => self.text = text.as_bytes(),
                Some(Part::Slot(name)) => {
                    let (prefix, mut index) = match walk.resolve(*name, owner) {
                        Resolved::Public(slot) => {
                            let next = self.public.len();
                            (b'p', *self.public.entry(slot).or_insert(next))
                        }
                        Resolved::Inner { owner, index } => {
                            let number = self.stack[owner].inner[index].get_or_insert_with(|| {
                                let next = self.next_inner;
                                self.next_inner += 1;
                                next
                            });
                            (b'i', *number)
                        }
                    };
                    loop {
                        self.number.push(b'0' + (index % 10) as u8);
                        index /= 10;
                        if index == 0 {
                            break;
                        }
                    }
                    self.number.push(prefix);
                }
                Some(Part::Child { template, public }) => {
                    let child = Walk {
                        parts: template.parts.iter(),
                        public: public
                            .iter()
                            .map(|(s, name)| (*s, walk.resolve(*name, owner)))
                            .collect(),
                        inner: vec![None; template.inner_count],
                    };
                    self.stack.push(child);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spelling(template: &Template) -> String {
        String::from_utf8(Spelling::new(template).collect()).unwrap()
    }

    fn variable(slot: Slot) -> Arc<Template> {
        let mut template = Template::default();
        template.text("Var(");
        template.slot(Name::Public(slot));
        template.text(",)");
        Arc::new(template)
    }

    #[test]
    fn repeated_children_refresh_private_slots_and_compose_public_names() {
        // Lam binds 7 in one child; 7 is also a *free* slot in its other child.
        // The caller maps that free slot to its own binder. Every occurrence of
        // Lam must retain a separate binder despite sharing the same template.
        let mut lam = Template::default();
        let bound = lam.fresh_inner();
        lam.text("Lam(bind");
        lam.slot(bound);
        lam.text(",");
        let var = variable(0);
        lam.child(Arc::clone(&var), BTreeMap::from([(0, bound)]));
        lam.text(",");
        lam.child(var, BTreeMap::from([(0, Name::Public(7))]));
        lam.text(")");
        let lam = Arc::new(lam);
        assert_eq!(spelling(&lam), "Lam(bindi0,Var(i0,),Var(p0,))");

        let mut pair = Template::default();
        let outer = pair.fresh_inner();
        pair.text("Pair(bind");
        pair.slot(outer);
        pair.text(",");
        pair.child(Arc::clone(&lam), BTreeMap::from([(7, outer)]));
        pair.text(",");
        pair.child(lam, BTreeMap::from([(7, Name::Public(99))]));
        pair.text(")");
        assert_eq!(
            spelling(&pair),
            "Pair(bindi0,Lam(bindi1,Var(i1,),Var(i0,)),Lam(bindi2,Var(i2,),Var(p0,)))"
        );
    }

    #[test]
    fn byte_order_matches_expanded_strings_including_decimal_slot_numbers() {
        let mut templates = Vec::new();
        let mut expected = Vec::new();
        for prefix in ["F", "F(", "é", "λ"] {
            for repeat in 0..12 {
                let mut template = Template::default();
                template.text(prefix);
                let mut text = prefix.to_owned();
                // Name order differs from occurrence order; numbering is by the latter.
                for i in 0..12 {
                    template.slot(Name::Public(99 - i));
                    template.text(",");
                    text.push_str(&format!("p{i},"));
                }
                template.slot(Name::Public(99 - repeat));
                text.push_str(&format!("p{repeat}"));
                assert_eq!(spelling(&template), text);
                templates.push(template);
                expected.push(text);
            }
        }
        for (i, a) in templates.iter().enumerate() {
            for (j, b) in templates.iter().enumerate() {
                assert_eq!(a.compare(b), expected[i].cmp(&expected[j]));
            }
        }
    }

    #[test]
    fn large_shared_tree_is_stored_and_compared_without_expansion() {
        let mut leaf = Template::default();
        let private = leaf.fresh_inner();
        leaf.slot(private);
        let mut tree = Arc::new(leaf);
        // More private slots than fit in u128, but just 131 shared templates.
        for _ in 0..130 {
            let mut parent = Template::default();
            parent.child(Arc::clone(&tree), BTreeMap::new());
            parent.child(tree, BTreeMap::new());
            tree = Arc::new(parent);
        }
        assert_eq!(
            String::from_utf8(Spelling::new(&tree).take(12).collect()).unwrap(),
            "i0i1i2i3i4i5"
        );
        let mut first = Template::default();
        first.text("A");
        first.child(Arc::clone(&tree), BTreeMap::new());
        let mut second = Template::default();
        second.text("B");
        second.child(tree, BTreeMap::new());
        assert_eq!(first.compare(&second), Ordering::Less);
        assert_eq!(first.compare(&first), Ordering::Equal);
    }

    #[test]
    fn ancestor_names_are_numbered_when_first_seen_in_a_descendant() {
        let mut parent = Template::default();
        let first = parent.fresh_inner();
        let second = parent.fresh_inner();
        let mut child = Template::default();
        let private = child.fresh_inner();
        child.slot(private);
        child.slot(Name::Public(0));
        let child = Arc::new(child);
        parent.child(Arc::clone(&child), BTreeMap::from([(0, second)]));
        parent.slot(first);
        parent.child(child, BTreeMap::from([(0, second)]));
        parent.slot(first);
        assert_eq!(spelling(&parent), "i0i1i2i3i1i2");
    }
}

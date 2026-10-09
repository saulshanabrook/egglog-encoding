//! Slotted matching frames: what a rule's atoms say about slots, joined.
//!
//! egglog finds the e-nodes a slotted pattern matches; this decides what the match
//! says about SLOTS. Every column of every matched node contributes equations
//! between *occurrences* of slots, and a frame is the closure of those equations:
//!
//! * `Node(a, s)` is slot `s` of the e-node matched at the atom rooted at variable `a`;
//! * `Var(v, t)` is slot `t` of the class variable `v` is bound to;
//! * `Lit("$x")` is a slot the pattern wrote, or one the right-hand side minted.
//!
//! An atom labelled `a` and rooted at `p` whose column carries `v` by the edge `e` says
//! `Node(a, e(t)) = Var(v, t)` for every class slot `t`; its root says `Node(a, s) =
//! Var(p, s)`; a literal `$x` at edge `e` says `Node(a, e(0)) = Lit("$x")`. The label
//! is the atom's own, since three atoms rooted at one variable match three e-nodes of
//! its class. A second occurrence of a variable comes with a symmetry of its class,
//! composed into the equation, so the match quantifies over the class's group.
//!
//! The equations say which occurrences are ONE slot; the CLIQUES say which are
//! DIFFERENT slots. A clique is a set of occurrences every two of which must be
//! distinct slots, so no two of them may share a block of the partition: the slots
//! of one e-node, the slots of one class, and the different literals. A frame is
//! consistent when no clique is broken.
//!
//! [`Frame::join`] unions two frames' equations and re-closes; it is associative and
//! commutative, so the atoms of a pattern may be joined in any order. Where two atoms
//! agree on a variable the join identifies
//! the occurrences on both sides, which is the reference's `unify`: a slot no
//! equation has tied down is a placeholder, not a name that was committed to. The
//! blocks of the closure are the pattern's slots, numbered in canonical order, and
//! [`Frame::refinements`] enumerates the consistent ways the remaining blocks may be
//! merged, which is the reference's `final_refine`.

use super::*;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

/// A spelling with a deterministic ordering key. The key preserves canonical
/// numbering across processes, but identity also compares the complete text:
/// hash collisions cannot identify different variables. Clones share ownership
/// of the text without a global interner, lock, or permanently leaked strings.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Name {
    order: u64,
    text: Arc<str>,
}

impl std::hash::Hash for Name {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.order.hash(state);
    }
}

impl Name {
    pub fn new(text: &str) -> Self {
        let mut h: u64 = 0xcbf29ce484222325;
        for b in text.bytes() {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x100000001b3);
        }
        Self {
            order: (h >> 1) | (u64::from(text.starts_with('$')) << 63),
            text: Arc::from(text),
        }
    }

    pub fn is_literal(&self) -> bool {
        self.text.starts_with('$')
    }
    pub fn as_str(&self) -> &str {
        &self.text
    }
}

/// Atom labels and class variables inhabit different identity domains.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomId(Name);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PVarId(Name);

macro_rules! name_id {
    ($ty:ident) => {
        impl $ty {
            pub fn new(text: &str) -> Self {
                Self(Name::new(text))
            }
        }
        impl From<&str> for $ty {
            fn from(text: &str) -> Self {
                Self::new(text)
            }
        }
        impl std::ops::Deref for $ty {
            type Target = Name;
            fn deref(&self) -> &Name {
                &self.0
            }
        }
        impl std::borrow::Borrow<Name> for $ty {
            fn borrow(&self) -> &Name {
                &self.0
            }
        }
        impl fmt::Display for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }
    };
}
name_id!(AtomId);
name_id!(PVarId);

impl From<&str> for Name {
    fn from(text: &str) -> Name {
        Name::new(text)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

/// Where a slot shows up in a match.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Occ {
    /// slot `s` of the e-node matched at the atom with this label
    Node(AtomId, i64),
    /// slot `t` of the class this variable is bound to
    Var(PVarId, i64),
    /// a literal the pattern wrote, or a slot the right-hand side minted
    Lit(Name),
}

impl fmt::Display for Occ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Occ::Node(a, s) => write!(f, "{a}.{s}"),
            Occ::Var(v, t) => write!(f, "{v}:{t}"),
            Occ::Lit(x) => write!(f, "{x}"),
        }
    }
}

/// How an occurrence reads its class's slots.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Reading {
    Identity,
    Fixed(Renaming),
    Group(Arc<Vec<Renaming>>),
}

impl Reading {
    fn slot(&self, slot: i64) -> Option<i64> {
        match self {
            Self::Identity => Some(slot),
            Self::Fixed(renaming) => renaming.get(&slot).copied(),
            Self::Group(_) => unreachable!("group readings are resolved by the frame"),
        }
    }
}

/// One column of an atom, as the pattern reads it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Binding {
    /// the atom's node is an invocation of this variable's class
    Root {
        var: PVarId,
        class_slots: SlotSet,
        reading: Reading,
    },
    /// a child column carrying a variable by an edge
    Child {
        var: PVarId,
        edge: Renaming,
        class_slots: SlotSet,
        reading: Reading,
    },
    /// a slot literal; `carried` when the column is an ordinary one, whose slot
    /// refinement may merge
    Lit {
        name: Name,
        edge: Renaming,
        carried: bool,
    },
    /// a payload leaf reached through its own class: it names node slots, nothing more
    Leaf { edge: Renaming },
}

pub type Bd = Boxed<Binding>;

/// A list of pattern variables and literals, by name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Names(pub Vec<Name>);

pub type Ns = Boxed<Names>;

/// A binding whose reading of its class is still open: the column's node slots meet
/// the variable's class slots through some element of the class's group, and which
/// one is settled by `refinements`, once the rest of the frame has pinned what it can
/// (C5). A further occurrence of a variable is bound this way, so the match quantifies
/// over the group without the query enumerating it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Pending {
    atom: AtomId,
    var: PVarId,
    /// class slot -> node slot; the identity on the class slots for a root
    edge: Renaming,
    group: Arc<Vec<Renaming>>,
}

/// The constraints a match has placed on slots so far, closed.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Frame {
    /// the partition of every occurrence named so far into the pattern's slots: two
    /// occurrences in one block are one slot, and `numbering` gives each block its
    /// number. Each block sorted, the blocks sorted by their least member. The
    /// ordinary cliques are implicit: `apart` reads them off the occurrences.
    blocks: Vec<Vec<Occ>>,
    /// per variable, the slots of its class: the domain of its renaming
    class_slots: BTreeMap<PVarId, SlotSet>,
    /// every literal, and whether refinement may merge a placeholder into its block
    literals: BTreeMap<Name, bool>,
    /// the variable whose class slots name the pattern's slots: a block holding
    /// `Var(anchor, t)` is slot `t`, the rest take the smallest free numbers
    anchor: Option<PVarId>,
    /// bindings whose reading is still open, resolved by `refinements`
    pending: Vec<Pending>,
    /// Nested matching keeps the outer class's slots and each node's fresh
    /// redundant slots distinct, even across atoms. None enables full aliasing.
    rigid: Option<BTreeSet<Occ>>,
}

/// Interned frames are immutable. Primitive reads share them instead of cloning
/// their partitions and slot maps; frame transformations still return owned frames.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fr(Arc<Frame>);

impl Fr {
    pub fn new(frame: Frame) -> Self {
        Self(Arc::new(frame))
    }
}

impl std::ops::Deref for Fr {
    type Target = Frame;

    fn deref(&self) -> &Frame {
        &self.0
    }
}

impl crate::core_relations::BaseValue for Fr {}

impl Frame {
    /// One atom's constraints: its label, exactly one `Root` among the bindings, and
    /// every other binding a column of that node. `None` when the columns already
    /// contradict each other.
    pub fn atom(label: &str, bindings: &[Binding]) -> Option<Frame> {
        Self::atom_impl(label, bindings, false)
    }

    /// An atom of a single nested pattern, with its freshly introduced slots
    /// added to the match-wide disequality clique. Anchor at the pattern's root
    /// before refinement to add the outer class's slots to that same clique.
    pub fn nested_atom(label: &str, bindings: &[Binding]) -> Option<Frame> {
        Self::atom_impl(label, bindings, true)
    }

    fn atom_impl(label: &str, bindings: &[Binding], nested: bool) -> Option<Frame> {
        let mut roots = bindings.iter().filter_map(|b| match b {
            Binding::Root {
                var,
                class_slots,
                reading,
            } => Some((var, class_slots, reading)),
            _ => None,
        });
        let (root_var, root_slots, root_reading) = roots.next()?;
        if roots.next().is_some() {
            return None;
        }
        let atom = AtomId::new(label);
        let mut node_slots: BTreeSet<i64> = BTreeSet::new();
        let mut eqs: Vec<(Occ, Occ)> = Vec::new();
        let mut occs: BTreeSet<Occ> = BTreeSet::new();
        let mut class_slots: BTreeMap<PVarId, SlotSet> = BTreeMap::new();
        let mut literals: BTreeMap<Name, bool> = BTreeMap::new();
        let mut pending: Vec<Pending> = Vec::new();

        // the root: the node is an invocation of the variable's class
        let cs = root_slots.clone();
        if let Reading::Group(group) = root_reading {
            // through some element of the class's group: decided later
            occs.extend(cs.iter().map(|&s| Occ::Var(root_var.clone(), s)));
            pending.push(Pending {
                atom: atom.clone(),
                var: root_var.clone(),
                edge: cs.iter().map(|&s| (s, s)).collect(),
                group: group.clone(),
            });
        } else {
            for &s in cs.iter() {
                let t = root_reading.slot(s)?;
                occs.insert(Occ::Var(root_var.clone(), t));
                eqs.push((Occ::Node(atom.clone(), s), Occ::Var(root_var.clone(), t)));
            }
        }
        node_slots.extend(cs.iter().copied());
        class_slots.insert(root_var.clone(), cs);

        for b in bindings {
            match b {
                Binding::Root { .. } => {}
                Binding::Child {
                    var,
                    edge,
                    class_slots: cls,
                    reading,
                } => {
                    let cs = cls.clone();
                    node_slots.extend(edge.values().copied());
                    if let Reading::Group(group) = reading {
                        occs.extend(cs.iter().map(|&t| Occ::Var(var.clone(), t)));
                        pending.push(Pending {
                            atom: atom.clone(),
                            var: var.clone(),
                            edge: edge.clone(),
                            group: group.clone(),
                        });
                    }
                    for &t in cs.iter() {
                        if matches!(reading, Reading::Group(_)) {
                            break;
                        }
                        let u = reading.slot(t)?;
                        // every class slot is an occurrence, so a variable's renaming is
                        // total on its class: a slot no edge reaches is a mint of its own
                        occs.insert(Occ::Var(var.clone(), u));
                        if let Some(&s) = edge.get(&t) {
                            eqs.push((Occ::Node(atom.clone(), s), Occ::Var(var.clone(), u)));
                        }
                    }
                    if let Some(prev) = class_slots.insert(var.clone(), cs.clone())
                        && prev != cs
                    {
                        return None;
                    }
                }
                Binding::Lit {
                    name,
                    edge,
                    carried,
                } => {
                    let s = *edge.get(&0)?;
                    node_slots.extend(edge.values().copied());
                    occs.insert(Occ::Lit(name.clone()));
                    eqs.push((Occ::Node(atom.clone(), s), Occ::Lit(name.clone())));
                    let entry = literals.entry(name.clone()).or_insert(false);
                    *entry |= carried;
                }
                Binding::Leaf { edge } => node_slots.extend(edge.values().copied()),
            }
        }
        occs.extend(node_slots.iter().map(|&s| Occ::Node(atom.clone(), s)));
        // enodes_applied preserves the invocation's live slots, but freshly
        // renames every other slot each time a nested node is entered.
        let rigid = nested.then(|| {
            node_slots
                .difference(root_slots)
                .map(|&s| Occ::Node(atom.clone(), s))
                .collect()
        });
        let frame = Frame {
            blocks: close(occs, &eqs),
            class_slots,
            literals,
            anchor: None,
            pending,
            rigid,
        };
        frame.consistent().then_some(frame)
    }

    /// Both frames' constraints together, closed; `None` when a clique breaks.
    /// Associative and commutative.
    pub fn join(&self, other: &Frame) -> Option<Frame> {
        let mut occs: BTreeSet<Occ> = BTreeSet::new();
        let mut eqs: Vec<(Occ, Occ)> = Vec::new();
        for block in self.blocks.iter().chain(&other.blocks) {
            occs.extend(block.iter().cloned());
            for pair in block.windows(2) {
                eqs.push((pair[0].clone(), pair[1].clone()));
            }
        }
        let mut class_slots = self.class_slots.clone();
        for (v, cs) in &other.class_slots {
            if let Some(prev) = class_slots.insert(v.clone(), cs.clone())
                && prev != *cs
            {
                return None;
            }
        }
        let mut literals = self.literals.clone();
        for (x, carried) in &other.literals {
            *literals.entry(x.clone()).or_insert(false) |= carried;
        }
        let frame = Frame {
            blocks: close(occs, &eqs),
            class_slots,
            literals,
            anchor: self.anchor.clone().or_else(|| other.anchor.clone()),
            pending: self.pending.iter().chain(&other.pending).cloned().collect(),
            rigid: match (&self.rigid, &other.rigid) {
                (None, None) => None,
                _ => Some(
                    self.rigid
                        .iter()
                        .chain(&other.rigid)
                        .flatten()
                        .cloned()
                        .collect(),
                ),
            },
        };
        frame.consistent().then_some(frame)
    }

    /// How many of a pending reading's node slots the frame has already tied to a name
    /// of the pattern's own: a literal, or a slot of the anchor's class.
    fn pinned(&self, p: &Pending) -> usize {
        p.edge
            .values()
            .filter(|&&s| {
                self.block_of(&Occ::Node(p.atom.clone(), s))
                    .is_some_and(|i| {
                        self.blocks[i].iter().any(|o| match o {
                            Occ::Lit(_) => true,
                            Occ::Var(v, _) => self.anchor.as_ref() == Some(v),
                            Occ::Node(..) => false,
                        })
                    })
            })
            .count()
    }

    /// This frame with more equations, re-closed, and the given readings still open;
    /// `None` when a clique breaks.
    fn with(&self, extra: &[(Occ, Occ)], pending: Vec<Pending>) -> Option<Frame> {
        let mut occs: BTreeSet<Occ> = BTreeSet::new();
        let mut eqs: Vec<(Occ, Occ)> = Vec::new();
        for block in &self.blocks {
            occs.extend(block.iter().cloned());
            for pair in block.windows(2) {
                eqs.push((pair[0].clone(), pair[1].clone()));
            }
        }
        for (a, b) in extra {
            occs.insert(a.clone());
            occs.insert(b.clone());
            eqs.push((a.clone(), b.clone()));
        }
        let frame = Frame {
            blocks: close(occs, &eqs),
            pending,
            ..self.clone()
        };
        frame.consistent().then_some(frame)
    }

    /// Every way to decide the open readings that keeps the frame consistent, each
    /// once. The rest of the frame usually pins the slots on both sides, so one
    /// element of the group fits, or none.
    fn resolved(&self) -> Vec<Frame> {
        if self.pending.is_empty() {
            return vec![self.clone()];
        }
        // the reading the rest of the frame constrains most goes first, so that the
        // elements it rules out are never multiplied by the others' -- a claim spells
        // its root's slots as literals, a rule anchors them, and each decided reading
        // pins the ones below it
        let pick = (0..self.pending.len())
            .max_by_key(|&i| self.pinned(&self.pending[i]))
            .expect("at least one pending reading");
        let first = &self.pending[pick];
        let rest: Vec<Pending> = self
            .pending
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != pick)
            .map(|(_, p)| p.clone())
            .collect();
        let mut out = Vec::new();
        let mut seen: BTreeSet<Vec<Vec<Occ>>> = BTreeSet::new();
        'elements: for g in first.group.iter() {
            let mut eqs = Vec::with_capacity(first.edge.len());
            for (t, s) in &first.edge {
                let Some(u) = g.get(t) else {
                    continue 'elements;
                };
                eqs.push((
                    Occ::Node(first.atom.clone(), *s),
                    Occ::Var(first.var.clone(), *u),
                ));
            }
            let Some(next) = self.with(&eqs, rest.clone()) else {
                continue;
            };
            for frame in next.resolved() {
                if seen.insert(frame.blocks.clone()) {
                    out.push(frame);
                }
            }
        }
        out
    }

    /// The frame spelled in this variable's slot names.
    pub fn anchored(&self, var: &str) -> Option<Frame> {
        let var = PVarId::new(var);
        let slots = self.class_slots.get(&var)?;
        let mut frame = Frame {
            anchor: Some(var.clone()),
            ..self.clone()
        };
        if let Some(rigid) = &mut frame.rigid {
            rigid.extend(slots.iter().map(|&s| Occ::Var(var.clone(), s)));
            if !frame.consistent() {
                return None;
            }
        }
        Some(frame)
    }

    /// Each block's slot number: the anchor's class slot where the block holds one,
    /// the smallest numbers the anchor does not use for the rest, in block order.
    fn numbering(&self) -> Vec<i64> {
        let mut out: Vec<Option<i64>> = vec![None; self.blocks.len()];
        let mut taken: BTreeSet<i64> = BTreeSet::new();
        if let Some(anchor) = &self.anchor {
            for (i, block) in self.blocks.iter().enumerate() {
                if let Some(t) = block.iter().find_map(|o| match o {
                    Occ::Var(v, t) if v == anchor => Some(*t),
                    _ => None,
                }) {
                    out[i] = Some(t);
                    taken.insert(t);
                }
            }
        }
        let mut next = 0;
        for slot in out.iter_mut() {
            if slot.is_none() {
                while taken.contains(&next) {
                    next += 1;
                }
                *slot = Some(next);
                next += 1;
            }
        }
        out.into_iter()
            .map(|s| s.expect("every block numbered"))
            .collect()
    }

    /// No clique has two members in one block.
    fn consistent(&self) -> bool {
        self.blocks.iter().all(|block| {
            self.rigid
                .as_ref()
                .is_none_or(|rigid| block.iter().filter(|o| rigid.contains(o)).take(2).count() < 2)
                && block
                    .iter()
                    .enumerate()
                    .all(|(i, o)| block[i + 1..].iter().all(|p| !apart(o, p)))
        })
    }

    /// The block an occurrence lies in.
    fn block_of(&self, occ: &Occ) -> Option<usize> {
        self.blocks
            .iter()
            .position(|c| c.binary_search(occ).is_ok())
    }

    /// The block of the variable occurrence `name:t`, without spelling it out.
    fn block_of_var(&self, name: &Name, t: i64) -> Option<usize> {
        self.blocks.iter().position(|c| {
            c.binary_search_by(|o| match o {
                Occ::Node(..) => Ordering::Less,
                Occ::Lit(_) => Ordering::Greater,
                Occ::Var(v, s) => (&v.0, *s).cmp(&(name, t)),
            })
            .is_ok()
        })
    }

    /// The block of the literal `name`, without spelling it out.
    fn block_of_lit(&self, name: &Name) -> Option<usize> {
        self.blocks.iter().position(|c| {
            c.binary_search_by(|o| match o {
                Occ::Lit(x) => x.cmp(name),
                _ => Ordering::Less,
            })
            .is_ok()
        })
    }

    /// The pattern slot an occurrence names.
    #[cfg(test)]
    fn slot(&self, occ: &Occ) -> Option<i64> {
        self.block_of(occ).map(|i| self.numbering()[i])
    }

    /// A variable's renaming into the pattern's slots, or a literal's `{0 -> slot}`:
    /// the numbering is computed once for the call, not once per slot.
    pub fn ren(&self, name: &str) -> Option<Renaming> {
        self.renaming(&Name::new(name))
    }

    fn renaming(&self, name: &Name) -> Option<Renaming> {
        let numbers = self.numbering();
        if name.is_literal() {
            if !self.literals.contains_key(name) {
                return None;
            }
            return Some(Renaming::from([(0, numbers[self.block_of_lit(name)?])]));
        }
        let cs = self.class_slots.get(name)?;
        cs.iter()
            .map(|&t| Some((t, numbers[self.block_of_var(name, t)?])))
            .collect()
    }

    /// Does the literal's slot lie in any of these variables' images?
    pub fn is_free(&self, lit: &str, vars: &[Name]) -> Option<bool> {
        let i = self.block_of_lit(&Name::new(lit))?;
        for v in vars {
            self.class_slots.get(v)?;
        }
        Some(
            self.blocks[i]
                .iter()
                .any(|o| matches!(o, Occ::Var(v, _) if vars.contains(v))),
        )
    }

    /// The same invocation: equal renamings into the pattern's slots.
    pub fn same(&self, a: &str, b: &str) -> Option<bool> {
        Some(self.ren(a)? == self.ren(b)?)
    }

    /// Fresh slots for a right-hand side, apart from everything the match named.
    pub fn mint(&self, names: &[Name]) -> Option<Frame> {
        let mut out = self.clone();
        for name in names {
            if !name.is_literal() || out.literals.contains_key(name) {
                return None;
            }
            out.literals.insert(name.clone(), false);
            out.blocks.push(vec![Occ::Lit(name.clone())]);
        }
        out.blocks.sort();
        Some(out)
    }

    /// A slot set with these literals' slots taken out: a built child's slots under a
    /// binder that binds them.
    pub fn without(&self, slots: &Renaming, bound: &[Name]) -> Option<Renaming> {
        let mut out = slots.clone();
        let numbers = self.numbering();
        for x in bound {
            out.remove(&numbers[self.block_of_lit(x)?]);
        }
        Some(out)
    }

    /// The free slots of a node built over these columns: the images of the
    /// uncovered columns, and of the covered ones and binder markers with the bound
    /// literals' slots taken out. As an identity renaming.
    pub fn node_slots(
        &self,
        uncovered: &[Name],
        covered: &[Name],
        bound: &[Name],
    ) -> Option<Renaming> {
        let mut slots: BTreeSet<i64> = BTreeSet::new();
        for v in uncovered {
            slots.extend(self.renaming(v)?.values().copied());
        }
        let mut inner: BTreeSet<i64> = BTreeSet::new();
        for v in covered {
            inner.extend(self.renaming(v)?.values().copied());
        }
        let numbers = self.numbering();
        for x in bound {
            inner.remove(&numbers[self.block_of_lit(x)?]);
        }
        slots.extend(inner);
        Some(slots.into_iter().map(|s| (s, s)).collect())
    }

    /// Whether refinement may merge this block: one a variable or a carried literal
    /// reaches. A redundant node slot or a binder's own slot stays as it is.
    fn carried(&self, block: &[Occ]) -> bool {
        block.iter().any(|o| match o {
            Occ::Var(..) => true,
            Occ::Lit(x) => self.literals.get(x).copied().unwrap_or(false),
            Occ::Node(..) => false,
        })
    }

    /// May these two blocks become one? Not when a clique has a member in each.
    fn mergeable(&self, i: usize, j: usize) -> bool {
        let (a, b) = (&self.blocks[i], &self.blocks[j]);
        if let Some(rigid) = &self.rigid
            && a.iter().any(|o| rigid.contains(o))
            && b.iter().any(|o| rigid.contains(o))
        {
            return false;
        }
        !a.iter().any(|o| b.iter().any(|p| apart(o, p)))
    }

    fn merged(&self, i: usize, j: usize) -> Frame {
        let mut out = self.clone();
        let mut b = out.blocks.remove(j.max(i));
        let a = &mut out.blocks[i.min(j)];
        a.append(&mut b);
        a.sort();
        out.blocks.sort();
        out
    }

    /// Every consistent way to decide the open readings and then to merge the blocks
    /// refinement may touch, each reading's unmerged frame before its mergings.
    /// This is the reference's `final_refine`; no valid alternatives are discarded.
    pub fn refinements(&self) -> Vec<Frame> {
        let mut out = Vec::new();
        let mut seen: BTreeSet<Vec<Vec<Occ>>> = BTreeSet::new();
        for frame in self.resolved() {
            if !seen.insert(frame.blocks.clone()) {
                continue;
            }
            out.push(frame.clone());
            frame.walk(&mut seen, &mut out);
        }
        out
    }

    fn walk(&self, seen: &mut BTreeSet<Vec<Vec<Occ>>>, out: &mut Vec<Frame>) {
        let cands: Vec<usize> = (0..self.blocks.len())
            .filter(|&i| self.carried(&self.blocks[i]))
            .collect();
        for (k, &i) in cands.iter().enumerate() {
            for &j in &cands[k + 1..] {
                if !self.mergeable(i, j) {
                    continue;
                }
                let next = self.merged(i, j);
                if !seen.insert(next.blocks.clone()) {
                    continue;
                }
                out.push(next.clone());
                next.walk(seen, out);
            }
        }
    }
}

/// The CLIQUES: must these two occurrences be different slots? Two slots of one
/// e-node, two slots of one class, or two different literals.
fn apart(o: &Occ, p: &Occ) -> bool {
    match (o, p) {
        (Occ::Node(a, s), Occ::Node(b, t)) => a == b && s != t,
        (Occ::Var(v, s), Occ::Var(w, t)) => v == w && s != t,
        (Occ::Lit(x), Occ::Lit(y)) => x != y,
        _ => false,
    }
}

/// The partition of `occs` generated by `eqs`: each block sorted, the blocks sorted.
fn close(occs: BTreeSet<Occ>, eqs: &[(Occ, Occ)]) -> Vec<Vec<Occ>> {
    let occs: Vec<Occ> = occs.into_iter().collect();
    let index: HashMap<&Occ, usize> = occs.iter().enumerate().map(|(i, o)| (o, i)).collect();
    let mut parent: Vec<usize> = (0..occs.len()).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    for (a, b) in eqs {
        let (ra, rb) = (find(&mut parent, index[a]), find(&mut parent, index[b]));
        if ra != rb {
            parent[ra.max(rb)] = ra.min(rb);
        }
    }
    // the root of each occurrence, before `occs` is consumed to fill the blocks
    let roots: Vec<usize> = (0..occs.len()).map(|i| find(&mut parent, i)).collect();
    drop(index);
    let mut blocks: HashMap<usize, Vec<Occ>> = HashMap::default();
    for (occ, root) in occs.into_iter().zip(roots) {
        blocks.entry(root).or_default().push(occ);
    }
    let mut out: Vec<Vec<Occ>> = blocks
        .into_values()
        .map(|mut c| {
            c.sort();
            c
        })
        .collect();
    out.sort();
    out
}

impl fmt::Display for Frame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, block) in self.blocks.iter().enumerate() {
            if i > 0 {
                write!(f, "; ")?;
            }
            write!(f, "{i}:")?;
            for o in block {
                write!(f, " {o}")?;
            }
        }
        for p in &self.pending {
            write!(f, "; ?{}~{}/{}", p.atom, p.var, p.group.len())?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug)]
pub struct FrameSort;

impl BaseSort for FrameSort {
    type Base = Fr;

    fn name(&self) -> &str {
        "Frame"
    }

    #[rustfmt::skip]
    fn register_primitives(&self, eg: &mut EGraph) {
        // a frame with no constraints
        add_primitive!(eg, "frame" = | | -> Fr { Fr::new(Frame::default()) });
        // one atom's constraints: `(atom "label" binding...)`, the label first because the
        // macro's varargs are of one sort
        for nested in [false, true] {
            eg.add_pure_primitive(
                AtomPrim {
                    nested,
                    string: eg.type_info.get_sort_by_name("String").expect("String sort").clone(),
                    binding: eg.type_info.get_sort_by_name("Binding").expect("Binding sort").clone(),
                    frame: eg.type_info.get_sort_by_name("Frame").expect("Frame sort").clone(),
                },
                None,
            );
        }
        // both frames' constraints, closed; fails where a clique breaks
        add_primitive!(eg, "frame-join" = |a: Fr, b: Fr| -?> Fr { a.join(&b).map(Fr::new) });
        // conditions, read after refinement
        add_primitive!(eg, "free"     = |f: Fr, lit: S, vs: Ns| -?> () { f.is_free(lit.as_str(), &vs.0.0).filter(|b| *b).map(|_| ()) });
        add_primitive!(eg, "not-free" = |f: Fr, lit: S, vs: Ns| -?> () { f.is_free(lit.as_str(), &vs.0.0).filter(|b| !*b).map(|_| ()) });
        // two variables are the same invocation
        add_primitive!(eg, "same"      = |f: Fr, a: S, b: S| -?> () { f.same(a.as_str(), b.as_str()).filter(|b| *b).map(|_| ()) });
        add_primitive!(eg, "bool-same" = |f: Fr, a: S, b: S| -?> bool { f.same(a.as_str(), b.as_str()) });
        // right-hand-side slots the pattern never pinned
        add_primitive!(eg, "mint" = |f: Fr, xs: Ns| -?> Fr { f.mint(&xs.0.0).map(Fr::new) });
        // the frame spelled in a variable's slot names -- the rule's root, so that its
        // renaming is the identity
        add_primitive!(eg, "anchor" = |f: Fr, v: S| -?> Fr { f.anchored(v.as_str()).map(Fr::new) });
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let frame = base_values.unwrap::<Fr>(value);
        termdag.lit(Literal::String(frame.0.to_string()))
    }
}

/// `(atom "label" binding...)`: one atom's constraints as a frame.
#[derive(Debug, Clone)]
struct AtomPrim {
    nested: bool,
    string: ArcSort,
    binding: ArcSort,
    frame: ArcSort,
}

impl Primitive for AtomPrim {
    fn name(&self) -> &str {
        if self.nested { "nested-atom" } else { "atom" }
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(AtomTypeConstraint {
            name: self.name().to_owned(),
            string: self.string.clone(),
            binding: self.binding.clone(),
            frame: self.frame.clone(),
            span: span.clone(),
        })
    }
}

impl PurePrim for AtomPrim {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let bv = state.base_values();
        let (label, rest) = args.split_first()?;
        let label = bv.unwrap::<S>(*label).0;
        let bindings: Vec<Binding> = rest.iter().map(|v| bv.unwrap::<Bd>(*v).0).collect();
        let frame = if self.nested {
            Frame::nested_atom(&label, &bindings)
        } else {
            Frame::atom(&label, &bindings)
        }?;
        Some(bv.get::<Fr>(Fr::new(frame)))
    }
}

struct AtomTypeConstraint {
    name: String,
    string: ArcSort,
    binding: ArcSort,
    frame: ArcSort,
    span: Span,
}

impl TypeConstraint for AtomTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        _typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let too_few = || {
            vec![constraint::impossible(
                constraint::ImpossibleConstraint::ArityMismatch {
                    atom: Atom {
                        span: self.span.clone(),
                        head: self.name.clone(),
                        args: arguments.to_vec(),
                    },
                    expected: 2,
                },
            )]
        };
        let Some((out, inputs)) = arguments.split_last() else {
            return too_few();
        };
        let Some((label, bindings)) = inputs.split_first() else {
            return too_few();
        };
        let mut cs: Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> = vec![
            constraint::assign(out.clone(), self.frame.clone()),
            constraint::assign(label.clone(), self.string.clone()),
        ];
        cs.extend(
            bindings
                .iter()
                .map(|b| constraint::assign(b.clone(), self.binding.clone())),
        );
        cs
    }
}

#[derive(Debug)]
pub struct BindingSort;

impl BaseSort for BindingSort {
    type Base = Bd;

    fn name(&self) -> &str {
        "Binding"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let binding = base_values.unwrap::<Bd>(value);
        termdag.lit(Literal::String(format!("{:?}", binding.0)))
    }
}

#[derive(Debug)]
pub struct NamesSort;

impl BaseSort for NamesSort {
    type Base = Ns;

    fn name(&self) -> &str {
        "Names"
    }

    #[rustfmt::skip]
    fn register_primitives(&self, eg: &mut EGraph) {
        add_primitive!(eg, "names" = [xs: S] -> Ns { Ns::new(Names(xs.map(|s| Name::new(s.as_str())).collect())) });
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let names = base_values.unwrap::<Ns>(value);
        let text: Vec<&str> = names.0.0.iter().map(|n| n.as_str()).collect();
        termdag.lit(Literal::String(text.join(" ")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn name_hash_collisions_do_not_identify_spellings() {
        let a = Name {
            order: 7,
            text: Arc::from("a"),
        };
        let b = Name {
            order: 7,
            text: Arc::from("b"),
        };
        assert_ne!(a, b);
        assert!(a < b);
        let distinct: hashbrown::HashSet<Name> = [a, b].into_iter().collect();
        assert_eq!(distinct.len(), 2);
        assert_eq!(Name::new("repeat"), Name::new("repeat"));
    }

    fn m(pairs: &[(i64, i64)]) -> Renaming {
        pairs.iter().copied().collect()
    }

    fn ident(slots: &[i64]) -> SlotSet {
        slots.iter().copied().collect()
    }

    fn root(v: &str, cs: &[i64]) -> Binding {
        Binding::Root {
            var: v.into(),
            class_slots: ident(cs),
            reading: Reading::Identity,
        }
    }

    fn child(v: &str, edge: &[(i64, i64)], cs: &[i64]) -> Binding {
        Binding::Child {
            var: v.into(),
            edge: m(edge),
            class_slots: ident(cs),
            reading: Reading::Identity,
        }
    }

    fn lit(x: &str, edge: &[(i64, i64)]) -> Binding {
        Binding::Lit {
            name: x.into(),
            edge: m(edge),
            carried: true,
        }
    }

    /// `p = (Sum R $x $y t1)`, `t1 = (Sing e1 e2)` on a node whose slots are 0..4.
    fn sum_sing() -> (Frame, Frame) {
        let sum = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                child("R", &[(0, 0)], &[0]),
                lit("$x", &[(0, 2)]),
                lit("$y", &[(0, 3)]),
                child("t1", &[(0, 1), (1, 2), (2, 3)], &[0, 1, 2]),
            ],
        )
        .unwrap();
        let sing = Frame::atom(
            "t1",
            &[
                root("t1", &[0, 1, 2]),
                child("e1", &[(0, 0)], &[0]),
                child("e2", &[(0, 1), (1, 2)], &[0, 1]),
            ],
        )
        .unwrap();
        (sum, sing)
    }

    #[test]
    fn join_is_commutative_and_identifies_shared_variables() {
        let (sum, sing) = sum_sing();
        let ab = sum.join(&sing).unwrap();
        let ba = sing.join(&sum).unwrap();
        assert_eq!(ab, ba);
        // e1 sits where t1's slot 0 does, which is p's node slot 1
        assert_eq!(
            ab.ren("e1").unwrap(),
            m(&[(0, ab.slot(&Occ::Node("p".into(), 1)).unwrap())])
        );
        // $x is t1's slot 1 seen from p, and e2's slot 0 seen from t1
        assert_eq!(ab.ren("$x").unwrap()[&0], ab.ren("e2").unwrap()[&0]);
        // the literals are apart, and the root's renaming is total on its class
        assert_ne!(ab.ren("$x").unwrap()[&0], ab.ren("$y").unwrap()[&0]);
        assert_eq!(ab.ren("p").unwrap().len(), 2);
    }

    #[test]
    fn a_node_cannot_have_two_of_its_slots_identified() {
        // (F a a) where a's class has one slot: both columns carry a, so the node's
        // two slots would have to be one -- refused
        let f = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                child("a", &[(0, 0)], &[0]),
                child("a", &[(0, 1)], &[0]),
            ],
        );
        assert!(f.is_none());
        // with symmetric edges it is fine: (F a a) matching F(c[0,1], c[1,0]) needs a sym
        let f = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                child("a", &[(0, 0), (1, 1)], &[0, 1]),
                Binding::Child {
                    var: "a".into(),
                    edge: m(&[(0, 1), (1, 0)]),
                    class_slots: ident(&[0, 1]),
                    reading: Reading::Fixed(m(&[(0, 1), (1, 0)])),
                },
            ],
        );
        assert!(f.is_some());
    }

    #[test]
    fn two_literals_never_become_one_slot() {
        let f = Frame::atom(
            "p",
            &[root("p", &[0]), lit("$x", &[(0, 0)]), lit("$y", &[(0, 0)])],
        );
        assert!(f.is_none());
        let g = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                lit("$x", &[(0, 0)]),
                lit("$y", &[(0, 1)]),
            ],
        )
        .unwrap();
        // refinement never merges them either
        assert!(g.refinements().iter().all(|r| r.ren("$x") != r.ren("$y")));
    }

    #[test]
    fn refinement_merges_only_what_the_pattern_left_open() {
        // (F a b) with a and b on one-slot classes at different node slots: the two
        // slots are distinct in the node, so no refinement merges them
        let f = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                child("a", &[(0, 0)], &[0]),
                child("b", &[(0, 1)], &[0]),
            ],
        )
        .unwrap();
        assert_eq!(f.refinements().len(), 1);
        // a redundant class slot of `a` that no edge reaches is a placeholder, and a
        // second such placeholder on `b` may be identified with it
        let g = Frame::atom(
            "p",
            &[
                root("p", &[0]),
                child("a", &[(0, 0)], &[0, 5]),
                child("b", &[(0, 0)], &[0, 7]),
            ],
        )
        .unwrap();
        let alts = g.refinements();
        assert_eq!(alts[0], g, "the identity comes first");
        assert!(
            alts.iter()
                .skip(1)
                .any(|r| r.ren("a").unwrap()[&5] == r.ren("b").unwrap()[&7])
        );
        assert!(
            alts.iter()
                .all(|r| r.ren("a").unwrap()[&5] != r.ren("a").unwrap()[&0]),
            "one node's slots stay apart"
        );
    }

    #[test]
    fn nested_matching_keeps_fresh_slots_apart_from_outer_slots() {
        let outer = [root("p", &[0]), child("t", &[], &[])];
        let inner = [root("t", &[]), child("a", &[(0, 3)], &[0])];
        let full = Frame::atom("outer", &outer)
            .unwrap()
            .join(&Frame::atom("inner", &inner).unwrap())
            .unwrap()
            .anchored("p")
            .unwrap();
        assert_eq!(full.refinements().len(), 2);
        let a = Frame::nested_atom("outer", &outer).unwrap();
        let b = Frame::nested_atom("inner", &inner).unwrap();
        let nested = a.join(&b).unwrap().anchored("p").unwrap();
        assert_eq!(nested, b.join(&a).unwrap().anchored("p").unwrap());
        assert_eq!(nested.refinements().len(), 1);
        assert_ne!(nested.ren("p").unwrap()[&0], nested.ren("a").unwrap()[&0]);
    }

    #[test]
    fn nested_matching_rejects_aliasing_forced_by_a_repeated_literal() {
        let outer = [root("p", &[0]), child("t", &[], &[]), lit("$x", &[(0, 0)])];
        let inner = [root("t", &[]), lit("$x", &[(0, 3)])];
        assert!(
            Frame::atom("outer", &outer)
                .unwrap()
                .join(&Frame::atom("inner", &inner).unwrap())
                .unwrap()
                .anchored("p")
                .is_some()
        );
        assert!(
            Frame::nested_atom("outer", &outer)
                .unwrap()
                .join(&Frame::nested_atom("inner", &inner).unwrap())
                .unwrap()
                .anchored("p")
                .is_none()
        );
    }

    #[test]
    fn nested_matching_preserves_sharing_already_in_an_edge() {
        let a = Frame::nested_atom(
            "outer",
            &[
                root("p", &[0]),
                child("t", &[(5, 0)], &[5]),
                lit("$x", &[(0, 0)]),
            ],
        )
        .unwrap();
        let b = Frame::nested_atom("inner", &[root("t", &[5]), lit("$x", &[(0, 5)])]).unwrap();
        assert_eq!(
            a.join(&b)
                .unwrap()
                .anchored("p")
                .unwrap()
                .refinements()
                .len(),
            1
        );
    }

    #[test]
    fn refinement_enumerates_all_six_slot_partitions() {
        // Six independent one-slot components have Bell(6) = 203 refinements.
        // A fixed prefix (formerly 64) silently loses distinct matches.
        let mut frame = Frame::default();
        let names: Vec<_> = (0..6).map(|i| format!("p{i}")).collect();
        for name in &names {
            frame = frame
                .join(&Frame::atom(name, &[root(name, &[0])]).unwrap())
                .unwrap();
        }
        let refinements = frame.refinements();
        assert_eq!(refinements[0], frame, "the identity comes first");
        let partitions: BTreeSet<Vec<i64>> = refinements
            .iter()
            .map(|r| names.iter().map(|v| r.ren(v).unwrap()[&0]).collect())
            .collect();
        assert_eq!(refinements.len(), 203);
        assert_eq!(partitions.len(), 203, "every refinement is distinct");
        assert!(
            partitions
                .iter()
                .any(|p| p[..5].iter().all(|s| *s == p[0]) && p[5] != p[0])
        );
    }

    #[test]
    fn atoms_rooted_at_one_variable_are_distinct_nodes() {
        // (Root r) with r = (Add $x b0), r = (Mul a1 b1), r = (Pair a2 b2), r's class
        // slotless: the three nodes' slots are three occurrence spaces, so $x (the Add's
        // slot 0) and a2 (the Pair's slot 0) are placeholders refinement may identify
        let add = Frame::atom(
            "r",
            &[
                root("r", &[]),
                lit("$x", &[(0, 0)]),
                child("b0", &[(0, 1)], &[0]),
            ],
        )
        .unwrap();
        let mul = Frame::atom(
            "r2",
            &[
                root("r", &[]),
                child("a1", &[(0, 0)], &[0]),
                child("b1", &[(0, 1)], &[0]),
            ],
        )
        .unwrap();
        let pair = Frame::atom(
            "r3",
            &[
                root("r", &[]),
                child("a2", &[(0, 0)], &[0]),
                child("b2", &[(0, 1)], &[0]),
            ],
        )
        .unwrap();
        let f = add.join(&mul).unwrap().join(&pair).unwrap();
        assert!(
            f.refinements()
                .iter()
                .any(|r| r.is_free("$x", &["a2".into()]) == Some(true))
        );
    }

    #[test]
    fn conditions_and_mints_read_the_refined_frame() {
        let (sum, sing) = sum_sing();
        let f = sum.join(&sing).unwrap();
        // $x is t1's second slot, which e2 carries: free in e2, not in e1
        assert_eq!(f.is_free("$x", &["e2".into()]), Some(true));
        assert_eq!(f.is_free("$x", &["e1".into()]), Some(false));
        let g = f.mint(&["$z".into()]).unwrap();
        let z = g.ren("$z").unwrap()[&0];
        assert_eq!(g.slot(&Occ::Lit("$z".into())), Some(z));
        // anchored at p, p's renaming is the identity and the mint stays apart from it
        let a = g.anchored("p").unwrap();
        assert!(a.ren("p").unwrap().iter().all(|(k, v)| k == v));
        assert!(
            !a.ren("p")
                .unwrap()
                .values()
                .any(|v| *v == a.ren("$z").unwrap()[&0])
        );
        assert!(
            f.mint(&["$x".into()]).is_none(),
            "a literal the pattern wrote is not fresh"
        );
        // node-slots: a Sing over e1 and a bound $x drops $x's slot from the covered side
        let slots = g
            .node_slots(&["e1".into()], &["$x".into(), "e2".into()], &["$x".into()])
            .unwrap();
        assert!(!slots.contains_key(&g.ren("$x").unwrap()[&0]));
        assert!(slots.contains_key(&g.ren("e1").unwrap()[&0]));
    }
}

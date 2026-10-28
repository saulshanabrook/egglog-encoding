//! Surface slotted terms in a [`TermDag`], and the finite bijections on slot
//! names that proofs rename them by.
//!
//! Internally a slot ID `n` is the term `Var("$n")`; proof display restores source
//! spellings and names generated slots with fresh `v0`, `v1`, … names.
//! A constructor application is an `App`
//! whose children are terms, with a binder column holding its bound slot as a
//! plain slot term. Payloads are literals. Pattern variables, which only appear
//! in rewrites, are `Var`s whose name does not start with `$`; a slot literal of
//! a rewrite, `$x`, is a `Var` too, so instantiating a pattern is one substitution.

use super::{HashMap, HashSet};
use crate::slotted::runtime::Renaming as SlotMap;
use egglog::{Term, TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// A shared supply for generated slot names. Negative slots are legal source
/// names too, so the counter alone does not establish freshness.
pub(super) struct FreshSlots {
    used: BTreeSet<i64>,
    next: i64,
}

impl FreshSlots {
    pub fn new(slots: impl IntoIterator<Item = i64>) -> Self {
        let used: BTreeSet<_> = slots.into_iter().collect();
        let next = used
            .first()
            .copied()
            .unwrap_or(0)
            .min(0)
            .checked_sub(1)
            .unwrap_or(-1);
        Self { used, next }
    }

    pub fn reserve(&mut self, slots: impl IntoIterator<Item = i64>) {
        self.used.extend(slots);
    }

    pub fn fresh(&mut self) -> i64 {
        loop {
            let slot = self.next;
            self.next = self.next.wrapping_sub(1);
            if self.used.insert(slot) {
                return slot;
            }
        }
    }
}

/// A finite permutation of slot names: the identity outside its support, and its
/// support is closed, so applying it to any term renames slots one to one. Identity
/// entries are never stored, so two renamings that act alike are equal.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Renaming(BTreeMap<i64, i64>);

impl Renaming {
    /// The permutation that fixes every slot.
    pub fn identity() -> Self {
        Self::default()
    }

    /// `None` unless the entries are a permutation: injective, with the same slots
    /// as keys and as values.
    pub fn new(entries: impl IntoIterator<Item = (i64, i64)>) -> Option<Self> {
        let map: BTreeMap<i64, i64> = entries.into_iter().filter(|(k, v)| k != v).collect();
        let keys: BTreeSet<i64> = map.keys().copied().collect();
        let targets: BTreeSet<i64> = map.values().copied().collect();
        (targets == keys).then_some(Self(map))
    }

    /// The encoding's partial renaming as a permutation, when it already is one.
    pub fn from_slot_map(map: &SlotMap) -> Option<Self> {
        Self::new(map.iter().map(|(k, v)| (*k, *v)))
    }

    /// The least permutation extending a partial injection: every slot the
    /// injection sends somewhere without being sent to is closed into a cycle by
    /// routing the orphaned target back to it. `None` if the entries are not
    /// injective.
    pub fn completing(entries: impl IntoIterator<Item = (i64, i64)>) -> Option<Self> {
        // the whole injection is validated first, fixed points included:
        // `0 -> 0, 1 -> 0` is not one, and dropping the fixed point would hide that
        let mut all: BTreeMap<i64, i64> = BTreeMap::new();
        for (k, v) in entries {
            if all.insert(k, v).is_some_and(|old| old != v) {
                return None;
            }
        }
        let targets: BTreeSet<i64> = all.values().copied().collect();
        if targets.len() != all.len() {
            return None;
        }
        let mut map: BTreeMap<i64, i64> = all.into_iter().filter(|(k, v)| k != v).collect();
        let targets: BTreeSet<i64> = map.values().copied().collect();
        // Walk each chain `a -> b -> ... -> z` whose end `z` is not a key and whose
        // start `a` is not a value; closing it with `z -> a` makes a cycle.
        let starts: Vec<i64> = map
            .keys()
            .filter(|k| !targets.contains(k))
            .copied()
            .collect();
        for start in starts {
            let mut end = start;
            while let Some(&next) = map.get(&end) {
                end = next;
            }
            map.insert(end, start);
        }
        Self::new(map)
    }

    /// Whether every slot is fixed.
    pub fn is_identity(&self) -> bool {
        self.0.is_empty()
    }

    /// Apply the permutation, leaving unlisted slots fixed.
    pub fn apply(&self, slot: i64) -> i64 {
        self.0.get(&slot).copied().unwrap_or(slot)
    }

    /// Reverse every mapping in the permutation.
    pub fn inverse(&self) -> Self {
        Self(self.0.iter().map(|(k, v)| (*v, *k)).collect())
    }

    /// `self ∘ other`: `other` applies first.
    pub fn compose(&self, other: &Self) -> Self {
        let keys: BTreeSet<i64> = self.0.keys().chain(other.0.keys()).copied().collect();
        Self(
            keys.into_iter()
                .map(|k| (k, self.apply(other.apply(k))))
                .filter(|(k, v)| k != v)
                .collect(),
        )
    }

    /// The least permutation that agrees with this one on `slots`.
    pub fn restricted(&self, slots: &BTreeSet<i64>) -> Self {
        Self::completing(
            self.0
                .iter()
                .filter(|(k, _)| slots.contains(k))
                .map(|(k, v)| (*k, *v)),
        )
        .expect("restricting a permutation keeps it injective")
    }

    /// The nonidentity mappings, ordered by source slot.
    pub fn entries(&self) -> impl Iterator<Item = (i64, i64)> + '_ {
        self.0.iter().map(|(k, v)| (*k, *v))
    }

    /// Does the renaming move any of these slots?
    pub fn moves_any(&self, slots: &BTreeSet<i64>) -> bool {
        self.0.keys().any(|k| slots.contains(k))
    }
}

impl fmt::Debug for Renaming {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Renaming {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (k, v)) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{k}->{v}")?;
        }
        write!(f, "}}")
    }
}

/// The slot term `$n`.
pub fn slot_term(dag: &mut TermDag, slot: i64) -> TermId {
    dag.var(format!("${slot}"))
}

/// The slot a term names, if it is a slot term.
pub fn slot_of(dag: &TermDag, term: TermId) -> Option<i64> {
    match dag.get(term) {
        Term::Var(name) => name.strip_prefix('$')?.parse().ok(),
        _ => None,
    }
}

/// Is this a rewrite's variable: a pattern variable or a slot literal? In a
/// pattern every `$name` is a literal, numbers included.
pub fn is_pattern_var(dag: &TermDag, term: TermId) -> bool {
    matches!(dag.get(term), Term::Var(_))
}

/// `m·t`: every slot occurrence renamed, bound and free alike.
pub fn rename(dag: &mut TermDag, m: &Renaming, term: TermId) -> TermId {
    if m.is_identity() {
        return term;
    }
    let mut memo = HashMap::default();
    rename_memo(dag, m, term, &mut memo)
}

fn rename_memo(
    dag: &mut TermDag,
    m: &Renaming,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&done) = memo.get(&term) {
        return done;
    }
    let out = match dag.get(term).clone() {
        Term::Lit(_) => term,
        Term::Var(_) => match slot_of(dag, term) {
            Some(slot) => slot_term(dag, m.apply(slot)),
            None => term,
        },
        Term::App(head, children) => {
            let children = children
                .into_iter()
                .map(|c| rename_memo(dag, m, c, memo))
                .collect();
            dag.app(head, children)
        }
    };
    memo.insert(term, out);
    out
}

/// Every slot occurring in the term, bound or free.
pub fn all_slots(dag: &TermDag, term: TermId) -> BTreeSet<i64> {
    let mut out = BTreeSet::new();
    let mut seen = HashSet::default();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match dag.get(t) {
            Term::Lit(_) => {}
            Term::Var(_) => {
                if let Some(slot) = slot_of(dag, t) {
                    out.insert(slot);
                }
            }
            Term::App(_, children) => stack.extend(children.iter().copied()),
        }
    }
    out
}

/// Substitute a rewrite's variables. `None` names a variable the substitution
/// leaves unbound.
pub fn instantiate(
    dag: &mut TermDag,
    pattern: TermId,
    substitution: &HashMap<String, TermId>,
) -> Result<TermId, String> {
    match dag.get(pattern).clone() {
        Term::Lit(_) => Ok(pattern),
        Term::Var(name) => substitution.get(&name).copied().ok_or(name),
        Term::App(head, children) => {
            let children = children
                .into_iter()
                .map(|c| instantiate(dag, c, substitution))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(dag.app(head, children))
        }
    }
}

/// The variables of a pattern, in order of first occurrence.
pub fn pattern_vars(dag: &TermDag, pattern: TermId) -> Vec<String> {
    fn walk(dag: &TermDag, t: TermId, out: &mut Vec<String>) {
        match dag.get(t) {
            Term::Lit(_) => {}
            Term::Var(name) => {
                if is_pattern_var(dag, t) && !out.contains(name) {
                    out.push(name.clone());
                }
            }
            Term::App(_, children) => {
                for &c in children {
                    walk(dag, c, out);
                }
            }
        }
    }
    let mut out = vec![];
    walk(dag, pattern, &mut out);
    out
}

/// Is `needle` a subterm of `haystack`?
pub fn is_subterm(dag: &TermDag, needle: TermId, haystack: TermId) -> bool {
    let mut seen = HashSet::default();
    let mut stack = vec![haystack];
    while let Some(t) = stack.pop() {
        if t == needle {
            return true;
        }
        if !seen.insert(t) {
            continue;
        }
        if let Term::App(_, children) = dag.get(t) {
            stack.extend(children.iter().copied());
        }
    }
    false
}

/// A permutation mapping each pair of terms exactly, or `None` if none exists.
pub(super) fn term_renaming(dag: &TermDag, pairs: &[(TermId, TermId)]) -> Option<Renaming> {
    let mut work = pairs.to_vec();
    let mut names = BTreeMap::new();
    while let Some((a, b)) = work.pop() {
        match (slot_of(dag, a), slot_of(dag, b)) {
            (Some(a), Some(b)) => {
                if names.insert(a, b).is_some_and(|old| old != b) {
                    return None;
                }
            }
            (None, None) => match (dag.get(a), dag.get(b)) {
                (Term::App(f, xs), Term::App(g, ys)) if f == g && xs.len() == ys.len() => {
                    work.extend(xs.iter().copied().zip(ys.iter().copied()))
                }
                (x, y) if x == y => (),
                _ => return None,
            },
            _ => return None,
        }
    }
    Renaming::completing(names)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(entries: &[(i64, i64)]) -> Renaming {
        Renaming::new(entries.iter().copied()).unwrap()
    }

    #[test]
    fn renamings_are_permutations() {
        let swap = r(&[(0, 1), (1, 0)]);
        assert!(swap.compose(&swap).is_identity());
        assert_eq!(swap.inverse(), swap);
        let cycle = r(&[(0, 1), (1, 2), (2, 0)]);
        assert_eq!(cycle.compose(&cycle.inverse()), Renaming::identity());
        assert_eq!(cycle.compose(&cycle), cycle.inverse());
        assert!(Renaming::new([(0, 1), (2, 1)]).is_none());
        assert!(Renaming::new([(0, 5)]).is_none());
        assert_eq!(
            Renaming::completing([(0, 5)]).unwrap(),
            r(&[(0, 5), (5, 0)])
        );
        assert_eq!(
            Renaming::completing([(0, 5), (5, 7)]).unwrap(),
            r(&[(0, 5), (5, 7), (7, 0)])
        );
        assert!(Renaming::completing([(0, 1), (2, 1)]).is_none());
        assert_eq!(cycle.restricted(&BTreeSet::from([0])), r(&[(0, 1), (1, 0)]));
        assert!(cycle.restricted(&BTreeSet::from([7])).is_identity());
    }

    #[test]
    fn renaming_a_term_touches_every_slot() {
        let mut dag = TermDag::default();
        let s0 = slot_term(&mut dag, 0);
        let s3 = slot_term(&mut dag, 3);
        let lam = dag.app("Lam".into(), vec![s0, s3]);
        let renamed = rename(&mut dag, &r(&[(0, 1), (1, 0), (3, 4), (4, 3)]), lam);
        assert_eq!(dag.to_string(renamed), "(Lam $1 $4)");
        assert_eq!(all_slots(&dag, renamed), BTreeSet::from([1, 4]));
    }

    #[test]
    fn patterns_instantiate_by_name() {
        let mut dag = TermDag::default();
        let x = dag.var("x".into());
        let lit = dag.var("$x".into());
        let pat = dag.app("Lam".into(), vec![lit, x]);
        assert_eq!(
            pattern_vars(&dag, pat),
            vec!["$x".to_string(), "x".to_string()]
        );
        let s7 = slot_term(&mut dag, 7);
        let null = dag.app("Null".into(), vec![]);
        let subst = HashMap::from_iter([("x".to_string(), null), ("$x".to_string(), s7)]);
        let t = instantiate(&mut dag, pat, &subst).unwrap();
        assert_eq!(dag.to_string(t), "(Lam $7 (Null))");
        assert!(is_subterm(&dag, null, t));
        let missing = HashMap::from_iter([("x".to_string(), null)]);
        assert_eq!(instantiate(&mut dag, pat, &missing), Err("$x".to_string()));
    }
    #[test]
    fn completing_validates_the_whole_injection() {
        assert!(Renaming::completing([(0, 0), (1, 0)]).is_none());
        assert!(Renaming::completing([(0, 1), (0, 2)]).is_none());
        let m = Renaming::completing([(0, 1), (1, 2)]).unwrap();
        assert_eq!((m.apply(0), m.apply(1), m.apply(2)), (1, 2, 0));
    }

    #[test]
    fn fresh_slots_skip_reserved_names_across_integer_boundary() {
        let mut fresh = FreshSlots::new([i64::MIN + 1, i64::MAX, -1]);
        fresh.reserve([i64::MIN]);
        assert_eq!(fresh.fresh(), i64::MAX - 1);
        assert_eq!(fresh.fresh(), i64::MAX - 2);
    }
}

//! Convert slotted runtime values to and from their proof terms. Renamings,
//! groups, and vectors use canonical map, set, and vector terms. `Frame`,
//! `Binding`, and `Names` use JSON string literals.
use super::*;
use egglog::sort::{map_term_to_btreemap, normalize_map_term};
use egglog::sort::{normalize_set_term, set_term_to_btreeset};
use egglog::sort::{vec_term, vec_term_children};
use serde::{Serialize, de::DeserializeOwned};
use std::borrow::Borrow;
use std::collections::BTreeMap;

pub(crate) fn int_from_term(termdag: &TermDag, id: TermId) -> Option<i64> {
    match termdag.get(id) {
        Term::Lit(Literal::Int(n)) => Some(*n),
        _ => None,
    }
}

pub(crate) fn string_from_term(termdag: &TermDag, id: TermId) -> Option<&str> {
    match termdag.get(id) {
        Term::Lit(Literal::String(s)) => Some(s),
        _ => None,
    }
}

/// `(map-of k0 v0 ...)` of `i64` literals as a renaming; `None` otherwise.
pub(crate) fn renaming_from_term(termdag: &TermDag, id: TermId) -> Option<Renaming> {
    map_term_to_btreemap(termdag, id)?
        .into_iter()
        .map(|(k, v)| Some((int_from_term(termdag, k.id())?, int_from_term(termdag, v)?)))
        .collect()
}

/// The canonical `(map-of ...)` term of a renaming.
pub(crate) fn renaming_to_term(termdag: &mut TermDag, renaming: &BTreeMap<i64, i64>) -> TermId {
    let flat: Vec<TermId> = renaming
        .iter()
        .flat_map(|(k, v)| [*k, *v])
        .map(|n| termdag.lit(Literal::Int(n)))
        .collect();
    normalize_map_term(termdag, &flat).expect("even arity")
}

/// A renaming term that is the identity on its domain, as a slot set.
pub(crate) fn slot_set_from_term(termdag: &TermDag, id: TermId) -> Option<SlotSet> {
    SlotSet::from_identity(&renaming_from_term(termdag, id)?)
}

/// `(set-of r0 ...)` of renamings as a group; `None` otherwise.
pub(crate) fn group_from_term(termdag: &TermDag, id: TermId) -> Option<Vec<Renaming>> {
    set_term_to_btreeset(termdag, id)?
        .into_iter()
        .map(|m| renaming_from_term(termdag, m.id()))
        .collect()
}

/// The canonical `(set-of ...)` term of a group.
pub(crate) fn group_to_term(
    termdag: &mut TermDag,
    group: &[impl Borrow<BTreeMap<i64, i64>>],
) -> TermId {
    let elements: Vec<TermId> = group
        .iter()
        .map(|m| renaming_to_term(termdag, m.borrow()))
        .collect();
    normalize_set_term(termdag, &elements)
}

/// `(vec-of r0 ...)` or `(vec-empty)` of renamings; `None` otherwise.
pub(crate) fn renamings_from_term(termdag: &TermDag, id: TermId) -> Option<Vec<Renaming>> {
    vec_term_children(termdag, id)?
        .into_iter()
        .map(|m| renaming_from_term(termdag, m))
        .collect()
}

/// The canonical vector term of renamings.
pub(crate) fn renamings_to_term(
    termdag: &mut TermDag,
    maps: impl IntoIterator<Item = impl Borrow<BTreeMap<i64, i64>>>,
) -> TermId {
    let elements: Vec<TermId> = maps
        .into_iter()
        .map(|m| renaming_to_term(termdag, m.borrow()))
        .collect();
    vec_term(termdag, elements)
}

/// A string literal holding `value`'s JSON. Callers must provide a deterministic
/// serialization so equal values have equal proof terms.
pub(crate) fn json_to_term<T: Serialize>(termdag: &mut TermDag, value: &T) -> TermId {
    let json = serde_json::to_string(value).expect("slotted values serialize");
    termdag.lit(Literal::String(json))
}

/// The value a JSON string literal holds; `None` for any other term or JSON.
pub(crate) fn json_from_term<T: DeserializeOwned>(termdag: &TermDag, id: TermId) -> Option<T> {
    serde_json::from_str(string_from_term(termdag, id)?).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renamings_and_groups_round_trip_canonically() {
        let mut termdag = TermDag::default();
        let a = Renaming::from([(1, 0), (0, 1)]);
        let b = Renaming::from([(0, 0), (1, 1)]);
        let ta = renaming_to_term(&mut termdag, &a);
        assert_eq!(renaming_from_term(&termdag, ta), Some(a.clone()));
        assert_eq!(termdag.to_string(ta), "(map-of 0 1 1 0)");
        let group = group_to_term(&mut termdag, &[a.clone(), b.clone()]);
        let again = group_to_term(&mut termdag, &[b.clone(), a.clone(), a.clone()]);
        assert_eq!(group, again);
        let mut parsed = group_from_term(&termdag, group).unwrap();
        parsed.sort();
        assert_eq!(parsed, vec![b.clone(), a.clone()]);
        let vec = renamings_to_term(&mut termdag, [a.clone(), b.clone()]);
        assert_eq!(
            renamings_from_term(&termdag, vec),
            Some(vec![a.clone(), b.clone()])
        );
        let empty = renamings_to_term(&mut termdag, Vec::<Renaming>::new());
        assert_eq!(renamings_from_term(&termdag, empty), Some(vec![]));
        assert!(renaming_from_term(&termdag, group).is_none());
        assert!(group_from_term(&termdag, vec).is_none());
        assert!(slot_set_from_term(&termdag, ta).is_none());
        let tb = renaming_to_term(&mut termdag, &b);
        assert_eq!(
            slot_set_from_term(&termdag, tb),
            Some([0, 1].into_iter().collect())
        );
    }
}

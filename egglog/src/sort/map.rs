use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapContainer {
    do_rebuild_keys: bool,
    do_rebuild_vals: bool,
    pub data: BTreeMap<Value, Value>,
}

impl MapContainer {
    /// A renaming: a map whose keys and values are slot names, so its contents
    /// never need rebuilding.
    pub(crate) fn renaming(data: BTreeMap<Value, Value>) -> Self {
        MapContainer {
            do_rebuild_keys: false,
            do_rebuild_vals: false,
            data,
        }
    }

    /// Whether this map's keys or values are e-classes, and so are rebuilt when
    /// the e-graph merges classes.
    pub(crate) fn rebuilds_contents(&self) -> bool {
        self.do_rebuild_keys || self.do_rebuild_vals
    }
}

impl ContainerValue for MapContainer {
    fn rebuild_contents(&mut self, rebuilder: &dyn ValueRebuilder) -> bool {
        let mut changed = false;
        if self.do_rebuild_keys {
            self.data = self
                .data
                .iter()
                .map(|(old, v)| {
                    let new = rebuilder.rebuild_val(*old);
                    changed |= *old != new;
                    (new, *v)
                })
                .collect();
        }
        if self.do_rebuild_vals {
            for old in self.data.values_mut() {
                let new = rebuilder.rebuild_val(*old);
                changed |= *old != new;
                *old = new;
            }
        }
        changed
    }
    fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        self.data.iter().flat_map(|(k, v)| [k, v]).copied()
    }
}

/// The entries of a flat `(map-of k0 v0 ...)` term as a Rust `BTreeMap` in
/// canonical key order, with `MapContainer`'s last-write-wins semantics on
/// duplicate keys; `None` for any other term.
fn map_term_to_btreemap<'a>(
    termdag: &'a TermDag,
    term_id: TermId,
) -> Option<BTreeMap<OrdTerm<'a>, TermId>> {
    match termdag.get(term_id) {
        Term::App(head, args) if head == "map-of" => map_of_args_to_btreemap(termdag, args),
        _ => None,
    }
}

/// Alternating `[k0, v0, ...]` `map-of` arguments as a `BTreeMap` (see
/// [`map_term_to_btreemap`]); `None` on odd arity.
fn map_of_args_to_btreemap<'a>(
    termdag: &'a TermDag,
    args: &[TermId],
) -> Option<BTreeMap<OrdTerm<'a>, TermId>> {
    if !args.len().is_multiple_of(2) {
        return None;
    }
    Some(
        args.chunks_exact(2)
            .map(|kv| (termdag.ord_term(kv[0]), kv[1]))
            .collect(),
    )
}

/// Flatten a map back to the `[k0, v0, k1, v1, ...]` argument list of its
/// canonical `(map-of ...)` term (sorted by key order, deduplicated).
fn map_term_args(map: BTreeMap<OrdTerm<'_>, TermId>) -> Vec<TermId> {
    map.into_iter().flat_map(|(k, v)| [k.id(), v]).collect()
}

/// Canonicalize alternating `[k0, v0, ...]` arguments to the flat
/// `(map-of ...)` term; `None` on odd arity.
fn normalize_map_term(termdag: &mut TermDag, args: &[TermId]) -> Option<TermId> {
    let flat = map_term_args(map_of_args_to_btreemap(termdag, args)?);
    Some(termdag.app("map-of".to_string(), flat))
}

/// `a ∘ b`, the map sending `x` to `a[b[x]]`: `b` applies first. Undefined
/// wherever either step is, so the result is keyed on
/// `{x ∈ dom(b) | b[x] ∈ dom(a)}`.
fn renaming_compose(
    a: &BTreeMap<Value, Value>,
    b: &BTreeMap<Value, Value>,
) -> BTreeMap<Value, Value> {
    b.iter()
        .filter_map(|(x, y)| a.get(y).map(|z| (*x, *z)))
        .collect()
}

/// `a ∘ b` where every key of `b` must survive; `None` if any is lost.
///
/// [`renaming_compose`] narrows silently when `b`'s image escapes `a`'s domain,
/// which is correct for composing partial maps but wrong wherever the result
/// becomes an *edge* of an e-node: an edge's domain must be its child's slot set,
/// so a narrowed edge misstates which slots the child has. Use this there, and
/// the rule declines instead of asserting something false.
fn renaming_compose_total(
    a: &BTreeMap<Value, Value>,
    b: &BTreeMap<Value, Value>,
) -> Option<BTreeMap<Value, Value>> {
    let out = renaming_compose(a, b);
    (out.len() == b.len()).then_some(out)
}

/// The inverse map; `None` unless the input is injective.
///
/// A renaming is a partial injection, so the inverse of a non-injective map is
/// not meaningful. Rejecting it turns a silently wrong answer into a rule that
/// does not fire.
fn renaming_inverse(m: &BTreeMap<Value, Value>) -> Option<BTreeMap<Value, Value>> {
    let out: BTreeMap<Value, Value> = m.iter().map(|(k, v)| (*v, *k)).collect();
    (out.len() == m.len()).then_some(out)
}

/// The identity map on `im(m)`.
///
/// A set of slots is represented as an identity renaming, so this is how to name
/// "the slots `m` maps onto" — the long way round being `(compose m (inverse m))`.
fn renaming_image(m: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    m.values().map(|v| (*v, *v)).collect()
}

/// The identity map on `dom(m)`; the counterpart of [`renaming_image`], spelled
/// the long way round as `(compose (inverse m) m)`.
fn renaming_domain(m: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    m.keys().map(|k| (*k, *k)).collect()
}

/// The entries two maps agree on.
///
/// A slot set is an identity renaming, so this is how one narrows: intersecting two
/// identity maps gives the identity on the intersection of their domains.
fn renaming_intersect(
    a: &BTreeMap<Value, Value>,
    b: &BTreeMap<Value, Value>,
) -> BTreeMap<Value, Value> {
    a.iter()
        .filter(|(k, v)| b.get(k) == Some(v))
        .map(|(k, v)| (*k, *v))
        .collect()
}

/// Union of partial maps; `None` if they disagree on a shared key.
fn renaming_union(
    a: &BTreeMap<Value, Value>,
    b: &BTreeMap<Value, Value>,
) -> Option<BTreeMap<Value, Value>> {
    let mut out = a.clone();
    for (k, v) in b {
        if out.insert(*k, *v).is_some_and(|old| old != *v) {
            return None;
        }
    }
    Some(out)
}

/// The least renaming `R` with `R ∘ second[i] = first[i]` for every `i`, given
/// the two halves flat as `[first..., second...]`.
///
/// Renamings are explicit partial maps, so a paired `(first[i], second[i])`
/// must carry exactly the same key set: a missing key means "no mapping", not
/// "identity". Each shared key `k` contributes `R(second[i][k]) = first[i][k]`.
///
/// `None` when the halves are unequal in length, when a pair's key sets
/// differ, or when the constraints make `R` non-functional or non-injective.
fn renaming_find_mapping<T: Copy + Ord>(maps: &[BTreeMap<T, T>]) -> Option<BTreeMap<T, T>> {
    if !maps.len().is_multiple_of(2) {
        return None;
    }
    let (first, second) = maps.split_at(maps.len() / 2);

    let mut mapping = BTreeMap::new();
    let mut inverse = BTreeMap::new();
    for (m1, m2) in first.iter().zip(second) {
        if m1.len() != m2.len() || !m1.keys().eq(m2.keys()) {
            return None;
        }
        for ((_, v1), (_, v2)) in m1.iter().zip(m2) {
            if mapping.insert(*v2, *v1).is_some_and(|prev| prev != *v1) {
                return None;
            }
            if inverse.insert(*v1, *v2).is_some_and(|prev| prev != *v2) {
                return None;
            }
        }
    }
    Some(mapping)
}

/// [`renaming_find_mapping`] extended to be *total* on a domain, minting a
/// fresh slot for every domain key the constraints leave unnamed.
///
/// Arguments come flat as `[avoid, domain, first..., second...]`. The
/// constraint part is solved exactly as in [`renaming_find_mapping`]; each
/// remaining key of `domain` is then named with the *smallest* non-negative
/// value not already spoken for, which keeps the result injective and disjoint
/// from `avoid`.
///
/// `None` on the same conditions as [`renaming_find_mapping`], or on fewer than
/// two leading maps.
fn renaming_find_mapping_total(maps: &[BTreeMap<i64, i64>]) -> Option<BTreeMap<i64, i64>> {
    let (head, pairs) = maps.split_at_checked(2)?;
    let (avoid, domain) = (&head[0], &head[1]);

    let mut mapping = renaming_find_mapping(pairs)?;

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
    Some(mapping)
}

/// Most namings `find-mappings-total` will build. Beyond this it truncates, so a
/// caller that must not miss one compares [`renaming_naming_total_count`] against
/// the vector's length.
pub(crate) const FIND_MAPPINGS_CAP: usize = 1024;

/// How many namings [`renaming_find_mappings_total`] would produce for `unnamed`
/// domain keys and `avail` reusable slots, without building any of them.
pub(crate) fn renaming_naming_count(unnamed: usize, avail: usize) -> u128 {
    // One key at a time: it either takes a fresh name, leaving the candidates
    // untouched, or one of the `avail` slots, leaving one fewer for the keys after it.
    match unnamed {
        0 => 1,
        u => renaming_naming_count(u - 1, avail).saturating_add(
            (avail as u128).saturating_mul(renaming_naming_count(u - 1, avail.saturating_sub(1))),
        ),
    }
}

/// What a naming chooses between: the mapping the constraints force, the domain
/// keys they leave unnamed, the slots those keys may reuse, and every slot already
/// spoken for.
///
/// Shared so the count and the enumeration cannot drift apart; a count that
/// disagreed with what was built would be worse than no count at all.
fn renaming_naming_parts(
    maps: &[BTreeMap<i64, i64>],
) -> Option<(BTreeMap<i64, i64>, Vec<i64>, Vec<i64>, BTreeSet<i64>)> {
    let (head, pairs) = maps.split_at_checked(2)?;
    let (avoid, domain) = (&head[0], &head[1]);
    let solved = renaming_find_mapping(pairs)?;

    let unnamed: Vec<i64> = domain
        .keys()
        .filter(|k| !solved.contains_key(k))
        .copied()
        .collect();
    let spoken_for: BTreeSet<i64> = solved
        .values()
        .chain(avoid.keys())
        .chain(avoid.values())
        .copied()
        .collect();
    // Reusing a slot this mapping already assigned would break injectivity, so the
    // candidates are the slots spoken for elsewhere.
    let candidates: Vec<i64> = spoken_for
        .iter()
        .filter(|s| !solved.values().any(|v| v == *s))
        .copied()
        .collect();
    Some((solved, unnamed, candidates, spoken_for))
}

/// How many namings [`renaming_find_mappings_total`] has to choose from, ignoring
/// its cap. Compare against the vector's length to see whether the cap truncated.
///
/// `None` on the same conditions as [`renaming_find_mapping`].
pub(crate) fn renaming_naming_total_count(maps: &[BTreeMap<i64, i64>]) -> Option<u128> {
    let (_, unnamed, candidates, _) = renaming_naming_parts(maps)?;
    Some(renaming_naming_count(unnamed.len(), candidates.len()))
}

/// [`renaming_find_mapping_total`] with every naming it could have chosen, not
/// only the minting one.
///
/// Minting decides that an unnamed domain key is DIFFERENT from every slot
/// already spoken for, since a fresh name differs from everything. That is one
/// branch of a choice, and the other -- the key naming a slot the pattern
/// already used -- is a match the minting solution cannot express. Each unnamed
/// key may therefore take a fresh name, or any slot in `avoid` this mapping has
/// not already used; results stay injective, as a renaming must be.
///
/// Element 0 is the minting solution, so reading index 0 is exactly
/// [`renaming_find_mapping_total`]. The order of the rest is deterministic: an
/// index is only meaningful if it names the same mapping every run.
///
/// Empty when the constraints are unsatisfiable. At most `cap` elements are
/// built; compare against [`renaming_naming_total_count`] to detect that a
/// caller's index space is too small to reach them all.
pub(crate) fn renaming_find_mappings_total(
    maps: &[BTreeMap<i64, i64>],
    cap: usize,
) -> Vec<BTreeMap<i64, i64>> {
    let Some((solved, unnamed, candidates, spoken_for)) = renaming_naming_parts(maps) else {
        return Vec::new();
    };

    let mut out = Vec::new();
    let mut mapping = solved;
    let mut used = spoken_for;
    // Depth-first over the keys in order, taking the fresh name first at every
    // level, which puts the all-minting solution at index 0.
    fn walk(
        keys: &[i64],
        candidates: &[i64],
        mapping: &mut BTreeMap<i64, i64>,
        used: &mut BTreeSet<i64>,
        cap: usize,
        out: &mut Vec<BTreeMap<i64, i64>>,
    ) {
        if out.len() >= cap {
            return;
        }
        let Some((&k, rest)) = keys.split_first() else {
            out.push(mapping.clone());
            return;
        };
        let mut fresh = 0;
        while used.contains(&fresh) {
            fresh += 1;
        }
        // `fresh` is the smallest slot not spoken for, so it is never a candidate and
        // the choices cannot repeat. Injectivity is the only thing left to check.
        for choice in std::iter::once(fresh).chain(candidates.iter().copied()) {
            if mapping.values().any(|v| *v == choice) {
                continue;
            }
            let added = used.insert(choice);
            mapping.insert(k, choice);
            walk(rest, candidates, mapping, used, cap, out);
            mapping.remove(&k);
            if added {
                used.remove(&choice);
            }
            if out.len() >= cap {
                return;
            }
        }
    }
    walk(
        &unnamed,
        &candidates,
        &mut mapping,
        &mut used,
        cap,
        &mut out,
    );
    out
}

/// Every way the slots of one match may be merged: the reference's `final_refine`
/// (`slotted-egraphs/src/rewrite/multipat.rs`) as a pure function.
///
/// `maps` is `[all, pattern, group...]`, read by KEY set:
/// - `all` — every slot in play, which each result is total on;
/// - `pattern` — the slots the PATTERN writes, as opposed to the ones minted for a
///   class's own slots;
/// - each remaining map — a set of slots known pairwise apart. One per matched e-node,
///   because a node's slots are distinct. This is what keeps a result injective: two
///   slots of one node can never merge, so composing a merge map onto a renaming
///   cannot collapse two of its keys.
///
/// Two slots the pattern writes are never merged. The pattern asked for two names, and
/// merging them would let a `not-free` side condition pass by renaming its two slots
/// together — capture rather than alpha-equivalence.
///
/// ELEMENT 0 IS THE IDENTITY, which is the one place this deliberately differs from
/// the reference: it recurses into the merged branch first, and order does not matter
/// there because every state is returned. Here the caller reads a result by INDEX out
/// of a finite relation, so putting the all-apart solution first means an index space
/// too small to reach the rest degrades to not refining at all, rather than to an
/// arbitrary merge.
///
/// At most `cap` results are built.
pub(crate) fn renaming_refine_namings(
    maps: &[BTreeMap<i64, i64>],
    cap: usize,
) -> Vec<BTreeMap<i64, i64>> {
    let Some((all_map, rest)) = maps.split_first() else {
        return Vec::new();
    };
    let Some((pattern_map, groups)) = rest.split_first() else {
        return Vec::new();
    };
    let all: Vec<i64> = all_map.keys().copied().collect();
    let pattern: BTreeSet<i64> = pattern_map.keys().copied().collect();

    // One disequality per pair within a group, so a node's slots stay apart.
    let mut diseq: BTreeSet<(i64, i64)> = BTreeSet::new();
    for g in groups {
        let ks: Vec<i64> = g.keys().copied().collect();
        for (i, &x) in ks.iter().enumerate() {
            for &y in &ks[i + 1..] {
                diseq.insert((x.min(y), x.max(y)));
            }
        }
    }

    fn find(uf: &BTreeMap<i64, i64>, mut x: i64) -> i64 {
        while let Some(&p) = uf.get(&x) {
            if p == x {
                break;
            }
            x = p;
        }
        x
    }

    fn apart(uf: &BTreeMap<i64, i64>, diseq: &BTreeSet<(i64, i64)>, x: i64, y: i64) -> bool {
        diseq.iter().any(|&(p, q)| {
            let (p, q) = (find(uf, p), find(uf, q));
            (p == x && q == y) || (p == y && q == x)
        })
    }

    fn walk(
        all: &[i64],
        pattern: &BTreeSet<i64>,
        uf: BTreeMap<i64, i64>,
        diseq: BTreeSet<(i64, i64)>,
        cap: usize,
        out: &mut Vec<BTreeMap<i64, i64>>,
    ) {
        if out.len() >= cap {
            return;
        }
        for (i, &a) in all.iter().enumerate() {
            for &b in &all[i + 1..] {
                let (x, y) = (find(&uf, a), find(&uf, b));
                if x == y || apart(&uf, &diseq, x, y) {
                    continue;
                }
                // `allows_directed_union`: the slot being REPLACED may not be one the
                // pattern writes. Try either direction, and if both are pattern slots
                // this pair is simply not decidable -- the reference's `continue`.
                let redirect = if !pattern.contains(&x) {
                    Some((x, y))
                } else if !pattern.contains(&y) {
                    Some((y, x))
                } else {
                    None
                };
                let Some((from, to)) = redirect else { continue };

                // apart first, so the identity lands at index 0
                let mut d = diseq.clone();
                d.insert((x.min(y), x.max(y)));
                walk(all, pattern, uf.clone(), d, cap, out);

                let mut u = uf.clone();
                u.insert(from, to);
                walk(all, pattern, u, diseq, cap, out);
                return;
            }
        }
        out.push(all.iter().map(|&s| (s, find(&uf, s))).collect());
    }

    let mut out = Vec::new();
    walk(&all, &pattern, BTreeMap::new(), diseq, cap, &mut out);
    out
}

/// A map from a key type to a value type supporting these primitives:
/// - `map-empty`
/// - `map-insert`
/// - `map-get`
/// - `map-contains`
/// - `map-not-contains`
/// - `map-remove`
/// - `map-length`
/// - `map-union`
/// - `map-intersect`
///
/// When the key and value sorts coincide, a map also reads as a partial
/// injection on a single space (a "renaming"), and these are registered too:
/// - `compose`, and `compose-total`, which refuses to drop a key
/// - `inverse` (also spelled `map-inverse`)
/// - `map-image` and `map-domain`, naming a renaming's two slot sets
/// - `find-mapping`
///
/// With `i64` keys a renaming also names slots, and the slotted-e-graph
/// primitives are registered:
/// - `find-mapping-total`
/// - `slotted-subst` and `slotted-subst-frame`, the two halves of one
///   substitution's result (see [`crate::sort::SLOTTED_SUBST`])
///
/// These are not in [`Presort::reserved_primitives`], so a program that never
/// declares a `Map` sort may still use the names itself.
#[derive(Clone, Debug)]
pub struct MapSort {
    name: String,
    key: ArcSort,
    value: ArcSort,
}

impl MapSort {
    pub fn key(&self) -> ArcSort {
        self.key.clone()
    }

    pub fn value(&self) -> ArcSort {
        self.value.clone()
    }
}

impl Presort for MapSort {
    fn presort_name() -> &'static str {
        "Map"
    }

    fn reserved_primitives() -> Vec<&'static str> {
        vec![
            "map-empty",
            "map-of",
            "map-insert",
            "map-get",
            "map-not-contains",
            "map-contains",
            "map-remove",
            "map-length",
        ]
    }

    fn make_sort(
        typeinfo: &mut TypeInfo,
        name: String,
        args: &[Expr],
    ) -> Result<ArcSort, TypeError> {
        if let [Expr::Var(k_span, k), Expr::Var(v_span, v)] = args {
            let k = typeinfo
                .get_sort_by_name(k)
                .ok_or(TypeError::UndefinedSort(k.clone(), k_span.clone()))?;
            let v = typeinfo
                .get_sort_by_name(v)
                .ok_or(TypeError::UndefinedSort(v.clone(), v_span.clone()))?;

            let out = Self {
                name,
                key: k.clone(),
                value: v.clone(),
            };
            Ok(out.to_arcsort())
        } else {
            panic!()
        }
    }
}

impl ContainerSort for MapSort {
    type Container = MapContainer;

    fn name(&self) -> &str {
        &self.name
    }

    fn inner_sorts(&self) -> Vec<ArcSort> {
        vec![self.key.clone(), self.value.clone()]
    }

    fn is_eq_container_sort(&self) -> bool {
        self.key.is_eq_sort()
            || self.value.is_eq_sort()
            || self.key.is_eq_container_sort()
            || self.value.is_eq_container_sort()
    }

    fn inner_values(
        &self,
        container_values: &ContainerValues,
        value: Value,
    ) -> Vec<(ArcSort, Value)> {
        let val = container_values
            .get_val::<MapContainer>(value)
            .unwrap()
            .clone();
        val.data
            .iter()
            .flat_map(|(k, v)| [(self.key.clone(), *k), (self.value.clone(), *v)])
            .collect()
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        let arc = self.clone().to_arcsort();

        // The proof "term form" of a map is the flat `(map-of k0 v0 k1 v1 ...)`
        // in canonical key order (like `set-of`/`vec-of`), matching
        // `reconstruct_termdag`. Each validator round-trips through a Rust
        // `BTreeMap` (see `map_term_to_btreemap`), so it evaluates map terms
        // with `MapContainer`'s semantics; `None` for a malformed map term
        // fails the proof.
        let map_empty_validator = |termdag: &mut TermDag, _args: &[TermId]| -> Option<TermId> {
            Some(termdag.app("map-of".into(), vec![]))
        };
        let map_insert_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [map, key, value] = args else {
                return None;
            };
            let mut map = map_term_to_btreemap(termdag, *map)?;
            map.insert(termdag.ord_term(*key), *value);
            let flat = map_term_args(map);
            Some(termdag.app("map-of".into(), flat))
        };
        let map_get_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [map, key] = args else { return None };
            map_term_to_btreemap(termdag, *map)?
                .get(&termdag.ord_term(*key))
                .copied()
        };
        let map_length_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [map] = args else { return None };
            let len = map_term_to_btreemap(termdag, *map)?.len() as i64;
            Some(termdag.lit(Literal::Int(len)))
        };
        let map_contains_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [map, key] = args else { return None };
            let contains =
                map_term_to_btreemap(termdag, *map)?.contains_key(&termdag.ord_term(*key));
            contains.then(|| termdag.lit(Literal::Unit))
        };
        let map_not_contains_validator =
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                let [map, key] = args else { return None };
                let contains =
                    map_term_to_btreemap(termdag, *map)?.contains_key(&termdag.ord_term(*key));
                (!contains).then(|| termdag.lit(Literal::Unit))
            };

        add_primitive_with_validator!(eg, "map-empty" = {self.clone(): MapSort} || -> @MapContainer (arc) { MapContainer {
            do_rebuild_keys: self.ctx.key.is_eq_sort() || self.ctx.key.is_eq_container_sort(),
            do_rebuild_vals: self.ctx.value.is_eq_sort() || self.ctx.value.is_eq_container_sort(),
            data: BTreeMap::new()
        } }, map_empty_validator);

        // `map-of` is the flat constructor used as the canonical term form. It
        // takes alternating key/value arguments, so it needs a custom type
        // constraint rather than the `add_primitive!` macro.
        eg.add_pure_primitive(
            MapOf {
                name: "map-of".to_string(),
                map: arc.clone(),
                key: self.key.clone(),
                value: self.value.clone(),
            },
            Some(std::sync::Arc::new(normalize_map_term)),
        );

        add_primitive_with_validator!(eg, "map-get"    = |    xs: @MapContainer (arc), x: # (self.key())                     | -?> # (self.value()) { xs.data.get(&x).copied() }, map_get_validator);
        add_primitive_with_validator!(eg, "map-insert" = |mut xs: @MapContainer (arc), x: # (self.key()), y: # (self.value())| -> @MapContainer (arc) {{ xs.data.insert(x, y); xs }}, map_insert_validator);
        add_primitive!(eg, "map-remove" = |mut xs: @MapContainer (arc), x: # (self.key())                     | -> @MapContainer (arc) {{ xs.data.remove(&x);   xs }});

        add_primitive_with_validator!(eg, "map-length"       = |xs: @MapContainer (arc)| -> i64 { xs.data.len() as i64 }, map_length_validator);
        add_primitive_with_validator!(eg, "map-contains"     = |xs: @MapContainer (arc), x: # (self.key())| -?> () { ( xs.data.contains_key(&x)).then_some(()) }, map_contains_validator);
        add_primitive_with_validator!(eg, "map-not-contains" = |xs: @MapContainer (arc), x: # (self.key())| -?> () { (!xs.data.contains_key(&x)).then_some(()) }, map_not_contains_validator);

        add_primitive!(eg, "map-union" = |xs: @MapContainer (arc), ys: @MapContainer (arc)| -?> @MapContainer (arc) { Some(MapContainer { data: renaming_union(&xs.data, &ys.data)?, ..xs }) });
        add_primitive!(eg, "map-intersect" = |xs: @MapContainer (arc), ys: @MapContainer (arc)| -> @MapContainer (arc) { MapContainer { data: renaming_intersect(&xs.data, &ys.data), ..xs } });

        // `map-contains` is a fact, so it cannot be combined with `or`/`and`; this
        // is the same test as a value, for use inside a `guard`.
        add_primitive!(eg, "bool-map-contains" = |xs: @MapContainer (arc), x: # (self.key())| -> bool { xs.data.contains_key(&x) });

        // With matching key and value sorts a map is a partial injection on one
        // space — a renaming, in the slotted-e-graph sense — so it composes and
        // inverts. `find-mapping` solves for the renaming carrying one tuple of
        // edges onto another; it is variadic, taking the two tuples flat.
        if self.key.name() == self.value.name() {
            add_primitive!(eg, "compose" = |a: @MapContainer (arc), b: @MapContainer (arc)| -> @MapContainer (arc) { MapContainer { data: renaming_compose(&a.data, &b.data), ..b } });
            add_primitive!(eg, "compose-total" = |a: @MapContainer (arc), b: @MapContainer (arc)| -?> @MapContainer (arc) { Some(MapContainer { data: renaming_compose_total(&a.data, &b.data)?, ..b }) });
            add_primitive!(eg, "inverse"     = |a: @MapContainer (arc)| -?> @MapContainer (arc) { Some(MapContainer { data: renaming_inverse(&a.data)?, ..a }) });
            add_primitive!(eg, "map-inverse" = |a: @MapContainer (arc)| -?> @MapContainer (arc) { Some(MapContainer { data: renaming_inverse(&a.data)?, ..a }) });
            add_primitive!(eg, "map-image"   = |a: @MapContainer (arc)| -> @MapContainer (arc) { MapContainer { data: renaming_image(&a.data), ..a } });
            add_primitive!(eg, "map-domain"  = |a: @MapContainer (arc)| -> @MapContainer (arc) { MapContainer { data: renaming_domain(&a.data), ..a } });
            add_primitive!(eg, "find-mapping" = {self.clone(): MapSort} [xs: @MapContainer (arc)] -?> @MapContainer (arc) {{
                let maps: Vec<BTreeMap<Value, Value>> = xs.map(|m| m.data).collect();
                Some(MapContainer {
                    do_rebuild_keys: self.ctx.key.is_eq_sort() || self.ctx.key.is_eq_container_sort(),
                    do_rebuild_vals: self.ctx.value.is_eq_sort() || self.ctx.value.is_eq_container_sort(),
                    data: renaming_find_mapping(&maps)?,
                })
            }});

            // Minting a fresh slot means naming one that is not in use, which
            // needs the slot space to be ordered and unbounded above.
            if self.key.name() == "i64" {
                add_primitive!(eg, "find-mapping-total" = {self.clone(): MapSort} [xs: @MapContainer (arc)] -?> @MapContainer (arc) {{
                    let bv = state.base_values();
                    let maps: Vec<BTreeMap<i64, i64>> = xs
                        .map(|m| m.data.iter().map(|(k, v)| (bv.unwrap::<i64>(*k), bv.unwrap::<i64>(*v))).collect())
                        .collect();
                    let solved = renaming_find_mapping_total(&maps)?;
                    Some(MapContainer {
                        do_rebuild_keys: false,
                        do_rebuild_vals: false,
                        data: solved.into_iter().map(|(k, v)| (bv.get::<i64>(k), bv.get::<i64>(v))).collect(),
                    })
                }});

                // How many namings `find-mappings-total` chooses between, before its
                // cap. A rule comparing this against `vec-length` sees that the cap
                // truncated, which silently losing namings would not show.
                add_primitive!(eg, "find-mappings-total-count" = {self.clone(): MapSort} [xs: @MapContainer (arc)] -?> i64 {{
                    let bv = state.base_values();
                    let maps: Vec<BTreeMap<i64, i64>> = xs
                        .map(|m| m.data.iter().map(|(k, v)| (bv.unwrap::<i64>(*k), bv.unwrap::<i64>(*v))).collect())
                        .collect();
                    renaming_naming_total_count(&maps).map(|n| n.min(i64::MAX as u128) as i64)
                }});

                // Substitution needs both a read (to extract a term) and a
                // write (to add the substituted one), so it is registered as a
                // `FullPrim`: see `crate::sort::slotted_subst`. Its result is an
                // invocation, so it takes two names to read one -- the class and
                // the renaming placing it in `body`'s frame.
                for half in [
                    crate::sort::slotted_subst::Half::Class,
                    crate::sort::slotted_subst::Half::Frame,
                ] {
                    eg.add_full_primitive(
                        crate::sort::slotted_subst::SlottedSubst {
                            half,
                            renaming: arc.clone(),
                            slot: self.key.clone(),
                        },
                        None,
                    );
                }
            }
        }
    }

    fn reconstruct_termdag(
        &self,
        _container_values: &ContainerValues,
        _value: Value,
        termdag: &mut TermDag,
        element_terms: Vec<TermId>,
    ) -> TermId {
        // Flat `(map-of k0 v0 k1 v1 ...)` in canonical key order, so proof
        // checking can reproduce it from terms alone (and the rebuild proof's
        // Congr indices are flat, like `set-of`/`vec-of`).
        normalize_map_term(termdag, &element_terms).expect("map elements come in key/value pairs")
    }

    fn rebuild_container_normalizer(&self) -> Option<(String, PrimitiveValidator)> {
        Some(("map-of".to_owned(), Arc::new(normalize_map_term)))
    }

    fn serialized_name(&self, _container_values: &ContainerValues, _: Value) -> String {
        "map-of".to_owned()
    }
}

/// The flat `map-of` constructor: takes alternating key/value arguments and
/// builds a map. Used as the canonical term form for maps (analogous to
/// `set-of`/`vec-of`). Needs a custom type constraint because its arguments
/// alternate between the key and value sorts.
#[derive(Clone)]
struct MapOf {
    name: String,
    map: ArcSort,
    key: ArcSort,
    value: ArcSort,
}

impl Primitive for MapOf {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(MapOfTypeConstraint {
            name: self.name.clone(),
            key: self.key.clone(),
            value: self.value.clone(),
            map: self.map.clone(),
            span: span.clone(),
        })
    }
}

impl PurePrim for MapOf {
    fn apply<'a, 'db>(&self, mut state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let mut data = BTreeMap::new();
        for chunk in args.chunks(2) {
            if let [k, v] = chunk {
                data.insert(*k, *v);
            }
        }
        let mc = MapContainer {
            do_rebuild_keys: self.key.is_eq_sort() || self.key.is_eq_container_sort(),
            do_rebuild_vals: self.value.is_eq_sort() || self.value.is_eq_container_sort(),
            data,
        };
        Some(state.register_container(mc))
    }
}

/// Type constraint for [`MapOf`]: an even number of inputs alternating between
/// the key and value sorts, producing the map sort.
struct MapOfTypeConstraint {
    name: String,
    key: ArcSort,
    value: ArcSort,
    map: ArcSort,
    span: Span,
}

impl TypeConstraint for MapOfTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        _typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let arity_mismatch = |expected: usize| {
            vec![constraint::impossible(
                constraint::ImpossibleConstraint::ArityMismatch {
                    atom: Atom {
                        span: self.span.clone(),
                        head: self.name.clone(),
                        args: arguments.to_vec(),
                    },
                    expected,
                },
            )]
        };
        let Some((out, inputs)) = arguments.split_last() else {
            return arity_mismatch(1);
        };
        if inputs.len() % 2 != 0 {
            return arity_mismatch(inputs.len() + 2);
        }
        let mut cs: Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> =
            vec![constraint::assign(out.clone(), self.map.clone())];
        for (i, arg) in inputs.iter().enumerate() {
            let sort = if i % 2 == 0 {
                self.key.clone()
            } else {
                self.value.clone()
            };
            cs.push(constraint::assign(arg.clone(), sort));
        }
        cs
    }
}

#[cfg(test)]
mod naming_tests {
    use super::*;

    fn m(pairs: &[(i64, i64)]) -> BTreeMap<i64, i64> {
        pairs.iter().copied().collect()
    }

    fn ident(slots: &[i64]) -> BTreeMap<i64, i64> {
        slots.iter().map(|&s| (s, s)).collect()
    }

    /// Reading index 0 must mean "did not refine", so that an index space too small to
    /// reach the rest degrades to today's behaviour rather than to an arbitrary merge.
    #[test]
    fn refine_element_zero_is_the_identity() {
        let out = renaming_refine_namings(&[ident(&[0, 1]), ident(&[]), ident(&[])], 64);
        assert_eq!(out[0], ident(&[0, 1]));
    }

    /// `allows_directed_union`: the slot being replaced may not be one the pattern
    /// writes, so two pattern slots have no direction available and never merge.
    #[test]
    fn refine_never_merges_two_pattern_slots() {
        let out = renaming_refine_namings(&[ident(&[0, 1]), ident(&[0, 1]), ident(&[])], 64);
        assert_eq!(
            out,
            vec![ident(&[0, 1])],
            "two pattern slots must stay apart"
        );
    }

    /// A node's slots are pairwise distinct, so a group forbids merging within it --
    /// which is what keeps a merge map composable with a renaming without collapsing
    /// two of its keys.
    #[test]
    fn refine_never_merges_two_slots_of_one_node() {
        let out = renaming_refine_namings(&[ident(&[0, 1]), ident(&[]), ident(&[0, 1])], 64);
        assert_eq!(
            out,
            vec![ident(&[0, 1])],
            "one node's slots must stay apart"
        );
    }

    /// The case the whole thing exists for: a minted slot may be identified with a
    /// pattern slot, and the pattern slot must be the one that survives.
    #[test]
    fn refine_merges_a_minted_slot_into_a_pattern_slot() {
        // 0 is the pattern's, 7 was minted, and nothing says they are apart
        let out = renaming_refine_namings(&[ident(&[0, 7]), ident(&[0]), ident(&[])], 64);
        assert_eq!(out.len(), 2, "apart and merged");
        assert_eq!(out[0], ident(&[0, 7]));
        assert_eq!(
            out[1],
            m(&[(0, 0), (7, 0)]),
            "the pattern slot survives, per `allows_directed_union`"
        );
    }

    /// Two minted slots have both directions available, so they merge; which of the
    /// two survives is not observable, but the partition is.
    #[test]
    fn refine_merges_two_minted_slots() {
        let out = renaming_refine_namings(&[ident(&[5, 9]), ident(&[]), ident(&[])], 64);
        assert_eq!(out.len(), 2);
        assert_eq!(out[0], ident(&[5, 9]));
        let merged = &out[1];
        assert_eq!(merged[&5], merged[&9], "one class");
    }

    /// Three free slots give the five partitions of a 3-set (Bell(3)), and the first
    /// is the all-apart one.
    #[test]
    fn refine_reaches_every_partition_of_three_free_slots() {
        let out = renaming_refine_namings(&[ident(&[1, 2, 3]), ident(&[]), ident(&[])], 64);
        let partitions: BTreeSet<Vec<Vec<i64>>> = out
            .iter()
            .map(|mp| {
                let mut by_rep: BTreeMap<i64, Vec<i64>> = BTreeMap::new();
                for (&k, &v) in mp {
                    by_rep.entry(v).or_default().push(k);
                }
                by_rep.into_values().collect()
            })
            .collect();
        assert_eq!(partitions.len(), 5, "Bell(3) = 5, got {out:?}");
        assert_eq!(out[0], ident(&[1, 2, 3]));
    }

    /// The cap truncates rather than growing without bound, and index 0 survives it.
    #[test]
    fn refine_respects_the_cap() {
        let out = renaming_refine_namings(&[ident(&[1, 2, 3]), ident(&[]), ident(&[])], 2);
        assert_eq!(out.len(), 2);
        assert_eq!(out[0], ident(&[1, 2, 3]));
    }

    /// The shape of the `M3` divergence: two atoms share one slot, and the second
    /// atom's other slot may either take a fresh name or the one the first atom's
    /// other child already occupies.
    fn m3_args() -> Vec<BTreeMap<i64, i64>> {
        let avoid = m(&[(0, 0), (1, 1)]); // pattern slots already named
        let domain = m(&[(0, 0), (2, 2)]); // this atom's node slots
        let first = m(&[(0, 0)]); // pattern side of the shared-variable constraint
        let second = m(&[(0, 0)]); // node side
        vec![avoid, domain, first, second]
    }

    #[test]
    fn index_zero_is_the_minting_solution() {
        let args = m3_args();
        let all = renaming_find_mappings_total(&args, 64);
        assert_eq!(all[0], renaming_find_mapping_total(&args).unwrap());
    }

    #[test]
    fn the_identification_is_offered() {
        let all = renaming_find_mappings_total(&m3_args(), 64);
        // node slot 2 takes a fresh name, or pattern slot 1
        assert_eq!(all, vec![m(&[(0, 0), (2, 2)]), m(&[(0, 0), (2, 1)])]);
    }

    #[test]
    fn every_naming_stays_injective() {
        for naming in renaming_find_mappings_total(&m3_args(), 64) {
            let vals: BTreeSet<i64> = naming.values().copied().collect();
            assert_eq!(vals.len(), naming.len(), "not injective: {naming:?}");
        }
    }

    #[test]
    fn the_order_is_stable() {
        let a = renaming_find_mappings_total(&m3_args(), 64);
        let b = renaming_find_mappings_total(&m3_args(), 64);
        assert_eq!(a, b);
    }

    #[test]
    fn the_count_matches_what_is_enumerated() {
        // one unnamed key, one reusable slot
        assert_eq!(renaming_naming_count(1, 1), 2);
        assert_eq!(renaming_find_mappings_total(&m3_args(), 64).len(), 2);
        assert_eq!(renaming_naming_count(0, 5), 1);
        // These are injective assignments, not set partitions. Two keys over two
        // reusable slots: fresh/fresh, fresh/a, fresh/b, a/fresh, b/fresh, a/b, b/a.
        assert_eq!(renaming_naming_count(2, 2), 7);

        // and the formula agrees with what is actually built
        let avoid = m(&[(0, 0), (1, 1), (2, 2)]);
        let domain = m(&[(5, 5), (6, 6), (7, 7)]);
        // paired maps share the edge position as key; the values are the two sides'
        // slots, so this pins node slot 5 onto pattern slot 0
        let args = vec![avoid, domain, m(&[(0, 0)]), m(&[(0, 5)])];
        let all = renaming_find_mappings_total(&args, 999);
        assert_eq!(all.len() as u128, renaming_naming_count(2, 2));
    }

    #[test]
    fn the_cap_truncates_rather_than_lying() {
        let all = renaming_find_mappings_total(&m3_args(), 1);
        assert_eq!(all.len(), 1);
        assert_eq!(all[0], renaming_find_mapping_total(&m3_args()).unwrap());
    }

    /// The chain, not one call: each atom's avoid-set is the previous atoms' image,
    /// so a later atom may name a slot an earlier one minted. This is the claim the
    /// per-atom design rests on -- that composing the choices reaches every way the
    /// atoms' slots could coincide, without any call refining an earlier answer.
    #[test]
    fn chaining_reaches_every_partition_of_three_slots() {
        // three atoms, each with a single unconstrained node slot and no pairs
        fn step(avoid: &BTreeMap<i64, i64>) -> Vec<BTreeMap<i64, i64>> {
            renaming_find_mappings_total(&[avoid.clone(), m(&[(0, 0)])], 64)
        }

        let mut partitions: BTreeSet<Vec<usize>> = BTreeSet::new();
        for a in step(&m(&[])) {
            let sa = a[&0];
            let avoid_b: BTreeMap<i64, i64> = [(sa, sa)].into_iter().collect();
            for b in step(&avoid_b) {
                let sb = b[&0];
                let mut avoid_c = avoid_b.clone();
                avoid_c.insert(sb, sb);
                for c in step(&avoid_c) {
                    let sc = c[&0];
                    // the partition the three choices induce, as block indices
                    let mut blocks = Vec::new();
                    let mut seen: Vec<i64> = Vec::new();
                    for s in [sa, sb, sc] {
                        let idx = seen.iter().position(|x| *x == s).unwrap_or_else(|| {
                            seen.push(s);
                            seen.len() - 1
                        });
                        blocks.push(idx);
                    }
                    partitions.insert(blocks);
                }
            }
        }
        // Bell(3) = 5: all distinct, any one pair together (three ways), all together
        assert_eq!(partitions.len(), 5, "reached {partitions:?}");
        assert!(partitions.contains(&vec![0, 1, 2]));
        assert!(partitions.contains(&vec![0, 0, 0]));
        assert!(partitions.contains(&vec![0, 0, 1]));
        assert!(partitions.contains(&vec![0, 1, 0]));
        assert!(partitions.contains(&vec![0, 1, 1]));
    }

    #[test]
    fn unsatisfiable_constraints_give_nothing() {
        let avoid = m(&[(0, 0)]);
        let domain = m(&[(0, 0)]);
        // the same node slot forced onto two different pattern slots
        let args = vec![avoid, domain, m(&[(0, 0), (1, 1)]), m(&[(0, 5), (1, 5)])];
        assert!(renaming_find_mappings_total(&args, 64).is_empty());
    }
}

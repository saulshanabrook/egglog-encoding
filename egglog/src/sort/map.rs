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

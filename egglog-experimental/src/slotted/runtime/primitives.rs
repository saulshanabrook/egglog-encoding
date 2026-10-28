//! Conversion between egglog values and the slotted algorithms.
use super::renaming::*;
use super::terms::*;
use super::*;
use std::collections::BTreeMap;

/// Decode a renaming's entries as slot numbers.
fn slot_map(bv: &BaseValues, m: &BTreeMap<Value, Value>) -> Renaming {
    m.iter()
        .map(|(k, v)| (bv.unwrap::<i64>(*k), bv.unwrap::<i64>(*v)))
        .collect()
}

fn slot_set(bv: &BaseValues, m: &BTreeMap<Value, Value>) -> Option<SlotSet> {
    SlotSet::from_identity(&slot_map(bv, m))
}

/// A solver's answer back as a renaming's entries.
fn value_map(bv: &BaseValues, m: impl IntoIterator<Item = (i64, i64)>) -> BTreeMap<Value, Value> {
    m.into_iter()
        .map(|(k, v)| (bv.get::<i64>(k), bv.get::<i64>(v)))
        .collect()
}

/// The renamings a sequence of values names, as slot maps; `None` if one of them
/// is not a map.
fn slot_maps(
    state: &PureState<'_, '_>,
    values: impl IntoIterator<Item = Value>,
) -> Option<Vec<Renaming>> {
    let (bv, cv) = (state.base_values(), state.container_values());
    values
        .into_iter()
        .map(|v| Some(slot_map(bv, &cv.get_val::<MapContainer>(v)?.data)))
        .collect()
}

/// A solver's slot maps registered as renamings, in order, for a vector of them.
fn register_renamings(
    state: &mut PureState<'_, '_>,
    maps: impl IntoIterator<Item = Renaming>,
) -> Vec<Value> {
    maps.into_iter()
        .map(|m| {
            let data = value_map(state.base_values(), m);
            state.register_container(map_container(data))
        })
        .collect()
}

fn value_maps(
    state: &PureState<'_, '_>,
    values: impl IntoIterator<Item = Value>,
) -> Option<Vec<Arc<BTreeMap<Value, Value>>>> {
    values
        .into_iter()
        .map(|v| {
            Some(Arc::clone(
                &state.container_values().get_val::<MapContainer>(v)?.data,
            ))
        })
        .collect()
}

fn intern_group(state: &mut PureState<'_, '_>, maps: Vec<BTreeMap<Value, Value>>) -> SetContainer {
    let data = maps
        .into_iter()
        .map(|m| state.register_container(map_container(m)))
        .collect();
    SetContainer {
        do_rebuild: false,
        data: Arc::new(data),
    }
}

/// The validator of a binding constructor: `parse` builds the binding from the
/// argument terms, and the result is the binding's term form.
fn binding_validator(
    parse: impl Fn(&TermDag, &[TermId]) -> Option<Binding> + Send + Sync + 'static,
) -> impl Fn(&mut TermDag, &[TermId]) -> Option<TermId> + Send + Sync + 'static {
    move |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let binding = parse(termdag, args)?;
        Some(binding_to_term(termdag, &binding))
    }
}

/// The validator of a primitive over renamings only (variadic): `f` on the
/// parsed renamings, the result as a renaming term.
fn renamings_validator(
    f: impl Fn(&[Renaming]) -> Option<Renaming> + Send + Sync + 'static,
) -> impl Fn(&mut TermDag, &[TermId]) -> Option<TermId> + Send + Sync + 'static {
    move |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let maps: Vec<Renaming> = args
            .iter()
            .map(|m| renaming_from_term(termdag, *m))
            .collect::<Option<_>>()?;
        let out = f(&maps)?;
        Some(renaming_to_term(termdag, &out))
    }
}

/// The validator of a primitive over a frame and names: `f` on the parsed
/// frame and the rest of the arguments, the result as a renaming term.
fn frame_renaming_validator(
    compute: impl Fn(&TermDag, &Frame, &[TermId]) -> Option<Renaming> + Send + Sync + 'static,
) -> impl Fn(&mut TermDag, &[TermId]) -> Option<TermId> + Send + Sync + 'static {
    move |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let (f, rest) = args.split_first()?;
        let frame = frame_from_term(termdag, *f)?;
        let out = compute(termdag, &frame, rest)?;
        Some(renaming_to_term(termdag, &out))
    }
}

fn var(termdag: &TermDag, id: TermId) -> Option<PVarId> {
    string_from_term(termdag, id).map(PVarId::new)
}

fn lit_binding(carried: bool) -> impl Fn(&TermDag, &[TermId]) -> Option<Binding> + Send + Sync {
    move |termdag: &TermDag, args: &[TermId]| -> Option<Binding> {
        let [x, e] = args else { return None };
        Some(Binding::Lit {
            name: Name::new(string_from_term(termdag, *x)?),
            edge: renaming_from_term(termdag, *e)?,
            carried,
        })
    }
}

#[rustfmt::skip]
pub(super) fn register_map(eg: &mut EGraph, arc: ArcSort) {
    add_primitive_with_validator!(eg, "map-intersect" = |xs: @MapContainer (arc), ys: @MapContainer (arc)| -> @MapContainer (arc) { map_container(map_intersect(&xs.data, &ys.data)) }, renamings_validator(|ms| { let [a,b] = ms else { return None }; Some(Renaming(map_intersect(&a.0,&b.0))) }));
    add_primitive_with_validator!(eg, "compose-total" = |a: @MapContainer (arc), b: @MapContainer (arc)| -?> @MapContainer (arc) { Some(map_container(compose_total(&a.data, &b.data)?)) }, renamings_validator(|ms| { let [a,b] = ms else { return None }; Some(Renaming(compose_total(&a.0,&b.0)?)) }));
    add_primitive_with_validator!(eg, "map-image" = |a: @MapContainer (arc)| -> @MapContainer (arc) { map_container(map_image(&a.data)) }, renamings_validator(|ms| { let [a] = ms else { return None }; Some(Renaming(map_image(&a.0))) }));
    add_primitive_with_validator!(eg, "map-domain" = |a: @MapContainer (arc)| -> @MapContainer (arc) { map_container(map_domain(&a.data)) }, renamings_validator(|ms| { let [a] = ms else { return None }; Some(Renaming(map_domain(&a.0))) }));
    // Slotted matching frames (`slotted/frame.rs`) read renamings off matched
    // e-nodes and hand renamings back: the bindings an `atom` is made of,
    // a variable's renaming out of a frame, and a built node's slot set.
    // Each validator parses the same arguments from their term forms (see
    // `super::terms`) and runs the same algorithm.
    add_primitive_with_validator!(eg, "root" = |v: S, cs: @MapContainer (arc)| -?> Bd {
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), free_vars: slot_set(state.base_values(), &cs.data)?, reading: Reading::Identity }))
    }, binding_validator(|termdag, args| {
        let [v, cs] = args else { return None };
        Some(Binding::Root { var: var(termdag, *v)?, free_vars: slot_set_from_term(termdag, *cs)?, reading: Reading::Identity })
    }));
    add_primitive_with_validator!(eg, "root" = |v: S, cs: @MapContainer (arc), sym: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), free_vars: slot_set(bv, &cs.data)?, reading: Reading::Fixed(slot_map(bv, &sym.data)) }))
    }}, binding_validator(|termdag, args| {
        let [v, cs, sym] = args else { return None };
        Some(Binding::Root { var: var(termdag, *v)?, free_vars: slot_set_from_term(termdag, *cs)?, reading: Reading::Fixed(renaming_from_term(termdag, *sym)?) })
    }));
    add_primitive_with_validator!(eg, "child" = |v: S, e: @MapContainer (arc), cs: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), free_vars: slot_set(bv, &cs.data)?, reading: Reading::Identity }))
    }}, binding_validator(|termdag, args| {
        let [v, e, cs] = args else { return None };
        Some(Binding::Child { var: var(termdag, *v)?, edge: renaming_from_term(termdag, *e)?, free_vars: slot_set_from_term(termdag, *cs)?, reading: Reading::Identity })
    }));
    add_primitive_with_validator!(eg, "child" = |v: S, e: @MapContainer (arc), cs: @MapContainer (arc), sym: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), free_vars: slot_set(bv, &cs.data)?, reading: Reading::Fixed(slot_map(bv, &sym.data)) }))
    }}, binding_validator(|termdag, args| {
        let [v, e, cs, sym] = args else { return None };
        Some(Binding::Child { var: var(termdag, *v)?, edge: renaming_from_term(termdag, *e)?, free_vars: slot_set_from_term(termdag, *cs)?, reading: Reading::Fixed(renaming_from_term(termdag, *sym)?) })
    }));
    add_primitive_with_validator!(eg, "lit" = |x: S, e: @MapContainer (arc)| -> Bd {
        Bd::new(Binding::Lit { name: Name::new(x.as_str()), edge: slot_map(state.base_values(), &e.data), carried: true })
    }, binding_validator(lit_binding(true)));
    add_primitive_with_validator!(eg, "bound" = |x: S, e: @MapContainer (arc)| -> Bd {
        Bd::new(Binding::Lit { name: Name::new(x.as_str()), edge: slot_map(state.base_values(), &e.data), carried: false })
    }, binding_validator(lit_binding(false)));
    add_primitive_with_validator!(eg, "leaf" = |e: @MapContainer (arc)| -> Bd {
        Bd::new(Binding::Leaf { edge: slot_map(state.base_values(), &e.data) })
    }, binding_validator(|termdag, args| {
        let [e] = args else { return None };
        Some(Binding::Leaf { edge: renaming_from_term(termdag, *e)? })
    }));
    add_primitive_with_validator!(eg, "ren" = |f: Fr, name: S| -?> @MapContainer (arc) {
        Some(map_container(value_map(state.base_values(), f.ren(name.as_str())?)))
    }, frame_renaming_validator(|termdag, f, args| {
        let [name] = args else { return None };
        f.ren(string_from_term(termdag, *name)?)
    }));
    add_primitive_with_validator!(eg, "without" = |f: Fr, slots: @MapContainer (arc), bound: Ns| -?> @MapContainer (arc) {{
        let bv = state.base_values();
        Some(map_container(value_map(bv, f.without(&slot_map(bv, &slots.data), &bound.0 .0)?)))
    }}, frame_renaming_validator(|termdag, f, args| {
        let [slots, bound] = args else { return None };
        f.without(&renaming_from_term(termdag, *slots)?, &names_from_term(termdag, *bound)?.0)
    }));
    add_primitive_with_validator!(eg, "node-slots" = |f: Fr, uncovered: Ns, covered: Ns, bound: Ns| -?> @MapContainer (arc) {
        Some(map_container(value_map(state.base_values(), f.node_slots(&uncovered.0 .0, &covered.0 .0, &bound.0 .0)?)))
    }, frame_renaming_validator(|termdag, f, args| {
        let [uncovered, covered, bound] = args else { return None };
        f.node_slots(&names_from_term(termdag, *uncovered)?.0, &names_from_term(termdag, *covered)?.0, &names_from_term(termdag, *bound)?.0)
    }));
    add_primitive_with_validator!(eg, "find-mapping-total" = {arc.clone(): ArcSort} [xs: @MapContainer (arc)] -?> @MapContainer (arc) {{
        let bv = state.base_values();
        let maps: Vec<Renaming> = xs.map(|m| slot_map(bv, &m.data)).collect();
        Some(map_container(value_map(bv, find_mapping_total(&maps)?)))
    }}, renamings_validator(find_mapping_total));

    // Substitution needs both a read (to extract a term) and a
    // write (to add the substituted one), so it is registered as a
    // `FullPrim`: see `super::subst`. Its result is an
    // invocation, so it takes two names to read one -- the class and
    // the renaming placing it in `body`'s frame.
    // The two halves are called with the same arguments in one action, so
    // they share what one call computes.
    let slot = eg.type_info().get_sort_by_name("i64").unwrap().clone();
    for half in [
        super::subst::Half::Class,
        super::subst::Half::Frame,
    ] {
        eg.add_full_primitive(
            super::subst::SlottedSubst {
                half,
                renaming: arc.clone(),
                slot: slot.clone(),
            },
            None,
        );
    }
}

#[rustfmt::skip]
pub(super) fn register_set(eg: &mut EGraph, arc: ArcSort, renaming: ArcSort) {
    add_primitive_with_validator!(eg, "group-restrict" = {arc.clone(): ArcSort} |s: @SetContainer (arc.clone()), cs: @MapContainer (renaming.clone())| -?> @SetContainer (arc.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(intern_group(&mut state, group::restrict(&maps, &cs.data)))
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [s, cs] = args else { return None };
        let (group, cs) = (group_from_term(termdag, *s)?, renaming_from_term(termdag, *cs)?);
        let out = group::restrict(&group, &cs.0);
        Some(group_to_term(termdag, &out))
    });
    add_primitive_with_validator!(eg, "group-close" = {arc.clone(): ArcSort} |s: @SetContainer (arc.clone())| -?> @SetContainer (arc.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(intern_group(&mut state, group::close(&maps)))
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [s] = args else { return None };
        let out = group::close(&group_from_term(termdag, *s)?);
        Some(group_to_term(termdag, &out))
    });
    add_primitive_with_validator!(eg, "coset-min" = {arc.clone(): ArcSort} |m: @MapContainer (renaming.clone()), s: @SetContainer (arc.clone())| -?> @MapContainer (renaming.clone()) {{
        let maps = slot_maps(&state, s.data.iter().copied())?;
        let m = slot_map(state.base_values(), &m.data);
        let least = group::coset_min(&m, &maps)?;
        Some(map_container(value_map(state.base_values(), least)))
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [m, s] = args else { return None };
        let (m, group) = (renaming_from_term(termdag, *m)?, group_from_term(termdag, *s)?);
        let least = group::coset_min(&m.0, &group)?;
        Some(renaming_to_term(termdag, &least))
    });
    // `(root "p" cs grp)` and `(child "v" e cs grp)`: a binding whose reading of
    // its class is any element of the group, decided by the frame once the rest
    // of the pattern has pinned what it can (C5); see `Frame::refinements`.
    add_primitive_with_validator!(eg, "root" = {arc.clone(): ArcSort} |v: S, cs: @MapContainer (renaming.clone()), grp: @SetContainer (arc.clone())| -?> Bd {{
        let group = slot_maps(&state, grp.data.iter().copied())?;
        let free_vars = slot_set(state.base_values(), &cs.data)?;
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), free_vars, reading: Reading::Group(Arc::new(group)) }))
    }}, binding_validator(|termdag, args| {
        let [v, cs, grp] = args else { return None };
        let group = group_from_term(termdag, *grp)?;
        Some(Binding::Root { var: var(termdag, *v)?, free_vars: slot_set_from_term(termdag, *cs)?, reading: Reading::Group(Arc::new(group)) })
    }));
    add_primitive_with_validator!(eg, "child" = {arc.clone(): ArcSort} |v: S, e: @MapContainer (renaming.clone()), cs: @MapContainer (renaming.clone()), grp: @SetContainer (arc.clone())| -?> Bd {{
        let group = slot_maps(&state, grp.data.iter().copied())?;
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), free_vars: slot_set(bv, &cs.data)?, reading: Reading::Group(Arc::new(group)) }))
    }}, binding_validator(|termdag, args| {
        let [v, e, cs, grp] = args else { return None };
        let group = group_from_term(termdag, *grp)?;
        Some(Binding::Child { var: var(termdag, *v)?, edge: renaming_from_term(termdag, *e)?, free_vars: slot_set_from_term(termdag, *cs)?, reading: Reading::Group(Arc::new(group)) })
    }));
    add_primitive_with_validator!(eg, "coset-same" = {arc.clone(): ArcSort} |m1: @MapContainer (renaming.clone()), m2: @MapContainer (renaming.clone()), s: @SetContainer (arc.clone())| -?> bool {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(group::coset_same(&m1.data, &m2.data, &maps))
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [m1, m2, s] = args else { return None };
        let (m1, m2) = (renaming_from_term(termdag, *m1)?, renaming_from_term(termdag, *m2)?);
        let same = group::coset_same(&m1.0, &m2.0, &group_from_term(termdag, *s)?);
        Some(termdag.lit(Literal::Bool(same)))
    });
    add_primitive_with_validator!(eg, "group-slot-closure" = {arc.clone(): ArcSort} |s: @SetContainer (arc.clone()), slots: @MapContainer (renaming.clone())| -?> @MapContainer (renaming.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(map_container(group::slot_closure(&maps, &slots.data)))
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [s, slots] = args else { return None };
        let (group, slots) = (group_from_term(termdag, *s)?, renaming_from_term(termdag, *slots)?);
        let out = group::slot_closure(&group, &slots.0);
        Some(renaming_to_term(termdag, &out))
    });

}

#[rustfmt::skip]
pub(super) fn register_vec(eg: &mut EGraph, arc: ArcSort) {
    // `(shape e1 e2 ...)`: the edges in canonical spelling, then the renaming from
    // that spelling back to the node's names; see `shape`.
    add_primitive_with_validator!(eg, "shape" = {arc.clone(): ArcSort} [xs: # (arc.inner_sorts()[0].clone())] -?> @VecContainer (arc) {{
        let maps = slot_maps(&state, xs)?;
        let data = register_renamings(&mut state, shape(&maps).into_maps());
        Some(VecContainer { do_rebuild: false, data })
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let maps: Vec<Renaming> = args.iter().map(|m| renaming_from_term(termdag, *m)).collect::<Option<_>>()?;
        Some(renamings_to_term(termdag, shape(&maps).into_maps()))
    });
}

#[rustfmt::skip]
pub(super) fn register_node_shape(eg: &mut EGraph, arc: ArcSort, groups: ArcSort) {
    // `(node-shape (vec-of e1 ...) (vec-of g1 ...))`: the canonical edges, the
    // renaming back to the node's names, then its symmetries; see `node_shape`.
    add_primitive_with_validator!(eg, "node-shape" = {arc.clone(): ArcSort} |es: @VecContainer (arc.clone()), gs: @VecContainer (groups.clone())| -?> @VecContainer (arc.clone()) {{
        let edges = slot_maps(&state, es.data.iter().copied())?;
        let mut groups = Vec::with_capacity(gs.data.len());
        for value in gs.data.iter().copied() {
            let set = state.container_values().get_val::<SetContainer>(value)?.data.clone();
            groups.push(slot_maps(&state, set.iter().copied())?);
        }
        let data = register_renamings(&mut state, node_shape(&edges, &groups).into_maps());
        Some(VecContainer { do_rebuild: false, data })
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [es, gs] = args else { return None };
        let edges = renamings_from_term(termdag, *es)?;
        let groups: Vec<Vec<Renaming>> = egglog::sort::vec_term_children(termdag, *gs)?
            .into_iter()
            .map(|g| group_from_term(termdag, g))
            .collect::<Option<_>>()?;
        Some(renamings_to_term(termdag, node_shape(&edges, &groups).into_maps()))
    });
}

#[rustfmt::skip]
pub(super) fn register_symmetries(eg: &mut EGraph, arc: ArcSort, set: ArcSort) {
    // the symmetries `node-shape` put after its first `n` entries
    add_primitive_with_validator!(eg, "symmetries-of" = {arc.clone(): ArcSort} |xs: @VecContainer (arc.clone()), n: i64| -?> @SetContainer (set.clone()) {{
        let n = usize::try_from(n).ok()?;
        Some(SetContainer { do_rebuild: false, data: std::sync::Arc::new(xs.data.get(n..)?.iter().copied().collect()) })
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [xs, n] = args else { return None };
        let n = usize::try_from(int_from_term(termdag, *n)?).ok()?;
        let elements = egglog::sort::vec_term_children(termdag, *xs)?;
        Some(egglog::sort::normalize_set_term(termdag, elements.get(n..)?))
    });
    // `(group-coset-reps grp pinned)`: the least element of each coset of the
    // pinned slots' stabilizer, sorted by content so that an index into the
    // vector means the same in every run and in a proof; see `group::coset_reps`.
    add_primitive_with_validator!(eg, "group-coset-reps" = {arc.clone(): ArcSort} |s: @SetContainer (set.clone()), pinned: @MapContainer (arc.inner_sorts()[0].clone())| -?> @VecContainer (arc.clone()) {{
        let values: Vec<Value> = s.data.iter().copied().collect();
        let maps = slot_maps(&state, values.iter().copied())?;
        let pinned = slot_map(state.base_values(), &pinned.data);
        let mut chosen: Vec<usize> = group::coset_reps(&maps, &pinned);
        chosen.sort_by(|&i, &j| maps[i].cmp(&maps[j]));
        Some(VecContainer { do_rebuild: false, data: chosen.into_iter().map(|i| values[i]).collect() })
    }}, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [s, pinned] = args else { return None };
        let maps = group_from_term(termdag, *s)?;
        let pinned = renaming_from_term(termdag, *pinned)?;
        let mut chosen: Vec<Renaming> = group::coset_reps(&maps, &pinned).into_iter().map(|i| maps[i].clone()).collect();
        chosen.sort();
        Some(renamings_to_term(termdag, chosen))
    });
}

#[rustfmt::skip]
pub(super) fn register_frame_vec(eg: &mut EGraph, arc: ArcSort) {
    add_primitive_with_validator!(eg, "refinements" = {arc.clone(): ArcSort} |f: Fr| -> @VecContainer (arc) { VecContainer {
        do_rebuild: false,
        data: f
            .refinements()
            .into_iter()
            .map(|g| state.base_values().get::<Fr>(Fr::new(g)))
            .collect(),
    } }, |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
        let [f] = args else { return None };
        let frames: Vec<TermId> = frame_from_term(termdag, *f)?
            .refinements()
            .iter()
            .map(|g| frame_to_term(termdag, g))
            .collect();
        Some(egglog::sort::vec_term(termdag, frames))
    });
}

/// `a ∘ b`, preserving every key of `b`; `None` if `im(b)` escapes `dom(a)`.
/// Use this for e-node edges, whose domain must remain the child's slot set.
fn compose_total<T: Copy + Ord>(a: &BTreeMap<T, T>, b: &BTreeMap<T, T>) -> Option<BTreeMap<T, T>> {
    let out = compose(a, b);
    (out.len() == b.len()).then_some(out)
}

/// The identity map on `im(m)`.
fn map_image<T: Copy + Ord>(m: &BTreeMap<T, T>) -> BTreeMap<T, T> {
    m.values().map(|v| (*v, *v)).collect()
}

/// The identity map on `dom(m)`; the counterpart of [`map_image`].
fn map_domain<T: Copy + Ord>(m: &BTreeMap<T, T>) -> BTreeMap<T, T> {
    m.keys().map(|k| (*k, *k)).collect()
}

/// The entries two maps agree on.
///
/// A slot set is an identity renaming, so this is how one narrows: intersecting two
/// identity maps gives the identity on the intersection of their domains.
fn map_intersect<T: Copy + Ord>(a: &BTreeMap<T, T>, b: &BTreeMap<T, T>) -> BTreeMap<T, T> {
    a.iter()
        .filter(|(k, v)| b.get(k) == Some(v))
        .map(|(k, v)| (*k, *v))
        .collect()
}

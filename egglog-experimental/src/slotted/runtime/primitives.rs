//! Conversion between egglog values and the slotted algorithms.
use super::renaming::*;
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

#[rustfmt::skip]
pub(super) fn register_map(eg: &mut EGraph, arc: ArcSort) {
        add_primitive!(eg, "map-intersect" = |xs: @MapContainer (arc), ys: @MapContainer (arc)| -> @MapContainer (arc) { map_container(map_intersect(&xs.data, &ys.data)) });
            add_primitive!(eg, "compose-total" = |a: @MapContainer (arc), b: @MapContainer (arc)| -?> @MapContainer (arc) { Some(map_container(compose_total(&a.data, &b.data)?)) });
            add_primitive!(eg, "map-image"   = |a: @MapContainer (arc)| -> @MapContainer (arc) { map_container(map_image(&a.data)) });

    add_primitive!(eg, "map-domain" = |a: @MapContainer (arc)| -> @MapContainer (arc) { map_container(map_domain(&a.data)) });
    // Slotted matching frames (`slotted/frame.rs`) read renamings off matched
    // e-nodes and hand renamings back: the bindings an `atom` is made of,
    // a variable's renaming out of a frame, and a built node's slot set.
    add_primitive!(eg, "root" = |v: S, cs: @MapContainer (arc)| -?> Bd {
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), free_vars: slot_set(state.base_values(), &cs.data)?, reading: Reading::Identity }))
    });
    add_primitive!(eg, "root" = |v: S, cs: @MapContainer (arc), sym: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), free_vars: slot_set(bv, &cs.data)?, reading: Reading::Fixed(slot_map(bv, &sym.data)) }))
    }});
    add_primitive!(eg, "child" = |v: S, e: @MapContainer (arc), cs: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), free_vars: slot_set(bv, &cs.data)?, reading: Reading::Identity }))
    }});
    add_primitive!(eg, "child" = |v: S, e: @MapContainer (arc), cs: @MapContainer (arc), sym: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), free_vars: slot_set(bv, &cs.data)?, reading: Reading::Fixed(slot_map(bv, &sym.data)) }))
    }});
    add_primitive!(eg, "lit" = |x: S, e: @MapContainer (arc)| -> Bd {
        Bd::new(Binding::Lit { name: Name::new(x.as_str()), edge: slot_map(state.base_values(), &e.data), carried: true })
    });
    add_primitive!(eg, "bound" = |x: S, e: @MapContainer (arc)| -> Bd {
        Bd::new(Binding::Lit { name: Name::new(x.as_str()), edge: slot_map(state.base_values(), &e.data), carried: false })
    });
    add_primitive!(eg, "leaf" = |e: @MapContainer (arc)| -> Bd {
        Bd::new(Binding::Leaf { edge: slot_map(state.base_values(), &e.data) })
    });
    add_primitive!(eg, "ren" = |f: Fr, name: S| -?> @MapContainer (arc) {
        Some(map_container(value_map(state.base_values(), f.ren(name.as_str())?)))
    });
    add_primitive!(eg, "without" = |f: Fr, slots: @MapContainer (arc), bound: Ns| -?> @MapContainer (arc) {{
        let bv = state.base_values();
        Some(map_container(value_map(bv, f.without(&slot_map(bv, &slots.data), &bound.0 .0)?)))
    }});
    add_primitive!(eg, "node-slots" = |f: Fr, uncovered: Ns, covered: Ns, bound: Ns| -?> @MapContainer (arc) {
        Some(map_container(value_map(state.base_values(), f.node_slots(&uncovered.0 .0, &covered.0 .0, &bound.0 .0)?)))
    });
    add_primitive!(eg, "find-mapping-total" = {arc.clone(): ArcSort} [xs: @MapContainer (arc)] -?> @MapContainer (arc) {{
        let bv = state.base_values();
        let maps: Vec<Renaming> = xs.map(|m| slot_map(bv, &m.data)).collect();
        Some(map_container(value_map(bv, find_mapping_total(&maps)?)))
    }});

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
    add_primitive!(eg, "group-restrict" = {arc.clone(): ArcSort} |s: @SetContainer (arc.clone()), cs: @MapContainer (renaming.clone())| -?> @SetContainer (arc.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(intern_group(&mut state, group::restrict(&maps, &cs.data)))
    }});
    add_primitive!(eg, "group-close" = {arc.clone(): ArcSort} |s: @SetContainer (arc.clone())| -?> @SetContainer (arc.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(intern_group(&mut state, group::close(&maps)))
    }});
    add_primitive!(eg, "group-coset-reps" = {arc.clone(): ArcSort} |s: @SetContainer (arc.clone()), pinned: @MapContainer (renaming.clone())| -?> @SetContainer (arc.clone()) {{
        let values: Vec<Value> = s.data.iter().copied().collect();
        let maps = slot_maps(&state, values.iter().copied())?;
        let pinned = slot_map(state.base_values(), &pinned.data);
        let data = group::coset_reps(&maps, &pinned).into_iter().map(|i| values[i]).collect();
        Some(SetContainer { do_rebuild: false, data: Arc::new(data) })
    }});
    add_primitive!(eg, "coset-min" = {arc.clone(): ArcSort} |m: @MapContainer (renaming.clone()), s: @SetContainer (arc.clone())| -?> @MapContainer (renaming.clone()) {{
        let maps = slot_maps(&state, s.data.iter().copied())?;
        let m = slot_map(state.base_values(), &m.data);
        let least = group::coset_min(&m, &maps)?;
        Some(map_container(value_map(state.base_values(), least)))
    }});
    // `(root "p" cs grp)` and `(child "v" e cs grp)`: a binding whose reading of
    // its class is any element of the group, decided by the frame once the rest
    // of the pattern has pinned what it can (C5); see `Frame::refinements`.
    add_primitive!(eg, "root" = {arc.clone(): ArcSort} |v: S, cs: @MapContainer (renaming.clone()), grp: @SetContainer (arc.clone())| -?> Bd {{
        let group = slot_maps(&state, grp.data.iter().copied())?;
        let free_vars = slot_set(state.base_values(), &cs.data)?;
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), free_vars, reading: Reading::Group(Arc::new(group)) }))
    }});
    add_primitive!(eg, "child" = {arc.clone(): ArcSort} |v: S, e: @MapContainer (renaming.clone()), cs: @MapContainer (renaming.clone()), grp: @SetContainer (arc.clone())| -?> Bd {{
        let group = slot_maps(&state, grp.data.iter().copied())?;
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), free_vars: slot_set(bv, &cs.data)?, reading: Reading::Group(Arc::new(group)) }))
    }});
    add_primitive!(eg, "coset-same" = {arc.clone(): ArcSort} |m1: @MapContainer (renaming.clone()), m2: @MapContainer (renaming.clone()), s: @SetContainer (arc.clone())| -?> bool {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(group::coset_same(&m1.data, &m2.data, &maps))
    }});
    add_primitive!(eg, "group-slot-closure" = {arc.clone(): ArcSort} |s: @SetContainer (arc.clone()), slots: @MapContainer (renaming.clone())| -?> @MapContainer (renaming.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(map_container(group::slot_closure(&maps, &slots.data)))
    }});

}

#[rustfmt::skip]
pub(super) fn register_vec(eg: &mut EGraph, arc: ArcSort) {
    // `(shape e1 e2 ...)`: the edges in canonical spelling, then the renaming from
    // that spelling back to the node's names; see `shape`.
    add_primitive!(eg, "shape" = {arc.clone(): ArcSort} [xs: # (arc.inner_sorts()[0].clone())] -?> @VecContainer (arc) {{
        let maps = slot_maps(&state, xs)?;
        let data = register_renamings(&mut state, shape(&maps).into_maps());
        Some(VecContainer { do_rebuild: false, data })
    }});
}

#[rustfmt::skip]
pub(super) fn register_node_shape(eg: &mut EGraph, arc: ArcSort, groups: ArcSort) {
    // `(node-shape (vec-of e1 ...) (vec-of g1 ...))`: the canonical edges, the
    // renaming back to the node's names, then its symmetries; see `node_shape`.
    add_primitive!(eg, "node-shape" = {arc.clone(): ArcSort} |es: @VecContainer (arc.clone()), gs: @VecContainer (groups.clone())| -?> @VecContainer (arc.clone()) {{
        let edges = slot_maps(&state, es.data.iter().copied())?;
        let mut groups = Vec::with_capacity(gs.data.len());
        for value in gs.data.iter().copied() {
            let set = state.container_values().get_val::<SetContainer>(value)?.data.clone();
            groups.push(slot_maps(&state, set.iter().copied())?);
        }
        let data = register_renamings(&mut state, node_shape(&edges, &groups).into_maps());
        Some(VecContainer { do_rebuild: false, data })
    }});
}

#[rustfmt::skip]
pub(super) fn register_symmetries(eg: &mut EGraph, arc: ArcSort, set: ArcSort) {
    // the symmetries `node-shape` put after its first `n` entries
    add_primitive!(eg, "symmetries-of" = {arc.clone(): ArcSort} |xs: @VecContainer (arc.clone()), n: i64| -?> @SetContainer (set.clone()) {{
        let n = usize::try_from(n).ok()?;
        Some(SetContainer { do_rebuild: false, data: std::sync::Arc::new(xs.data.get(n..)?.iter().copied().collect()) })
    }});
}

#[rustfmt::skip]
pub(super) fn register_frame_vec(eg: &mut EGraph, arc: ArcSort) {
    add_primitive!(eg, "refinements" = {arc.clone(): ArcSort} |f: Fr| -> @VecContainer (arc) { VecContainer {
        do_rebuild: false,
        data: f
            .refinements()
            .into_iter()
            .map(|g| state.base_values().get::<Fr>(Fr::new(g)))
            .collect(),
    } });
}

/// `a ∘ b`, preserving every key of `b`; `None` if `im(b)` escapes `dom(a)`.
/// Use this for e-node edges, whose domain must remain the child's slot set.
fn compose_total(
    a: &BTreeMap<Value, Value>,
    b: &BTreeMap<Value, Value>,
) -> Option<BTreeMap<Value, Value>> {
    let out = compose(a, b);
    (out.len() == b.len()).then_some(out)
}

/// The identity map on `im(m)`.
fn map_image(m: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    m.values().map(|v| (*v, *v)).collect()
}

/// The identity map on `dom(m)`; the counterpart of [`map_image`].
fn map_domain(m: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    m.keys().map(|k| (*k, *k)).collect()
}

/// The entries two maps agree on.
///
/// A slot set is an identity renaming, so this is how one narrows: intersecting two
/// identity maps gives the identity on the intersection of their domains.
fn map_intersect(a: &BTreeMap<Value, Value>, b: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    a.iter()
        .filter(|(k, v)| b.get(k) == Some(v))
        .map(|(k, v)| (*k, *v))
        .collect()
}

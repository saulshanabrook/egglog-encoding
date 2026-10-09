//! Conversion between egglog values and the slotted algorithms.
use super::renaming::*;
use super::*;
use std::collections::BTreeMap;

/// A renaming's entries as slot numbers, which is what the solvers in this file
/// work on.
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
            state.register_container(MapContainer::renaming(data))
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
        .map(|m| state.register_container(MapContainer::renaming(m)))
        .collect();
    SetContainer {
        do_rebuild: false,
        data: Arc::new(data),
    }
}

#[rustfmt::skip]
pub(super) fn register_map(eg: &mut EGraph, map: &MapSort, arc: ArcSort) {
    // Slotted matching frames (`slotted/frame.rs`) read renamings off matched
    // e-nodes and hand renamings back: the bindings an `atom` is made of,
    // a variable's renaming out of a frame, and a built node's slot set.
    add_primitive!(eg, "root" = |v: S, cs: @MapContainer (arc)| -?> Bd {
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), class_slots: slot_set(state.base_values(), &cs.data)?, reading: Reading::Identity }))
    });
    add_primitive!(eg, "root" = |v: S, cs: @MapContainer (arc), sym: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), class_slots: slot_set(bv, &cs.data)?, reading: Reading::Fixed(slot_map(bv, &sym.data)) }))
    }});
    add_primitive!(eg, "child" = |v: S, e: @MapContainer (arc), cs: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), class_slots: slot_set(bv, &cs.data)?, reading: Reading::Identity }))
    }});
    add_primitive!(eg, "child" = |v: S, e: @MapContainer (arc), cs: @MapContainer (arc), sym: @MapContainer (arc)| -?> Bd {{
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), class_slots: slot_set(bv, &cs.data)?, reading: Reading::Fixed(slot_map(bv, &sym.data)) }))
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
        Some(MapContainer::renaming(value_map(state.base_values(), f.ren(name.as_str())?)))
    });
    add_primitive!(eg, "without" = |f: Fr, slots: @MapContainer (arc), bound: Ns| -?> @MapContainer (arc) {{
        let bv = state.base_values();
        Some(MapContainer::renaming(value_map(bv, f.without(&slot_map(bv, &slots.data), &bound.0 .0)?)))
    }});
    add_primitive!(eg, "node-slots" = |f: Fr, uncovered: Ns, covered: Ns, bound: Ns| -?> @MapContainer (arc) {
        Some(MapContainer::renaming(value_map(state.base_values(), f.node_slots(&uncovered.0 .0, &covered.0 .0, &bound.0 .0)?)))
    });
    add_primitive!(eg, "find-mapping-total" = {map.clone(): MapSort} [xs: @MapContainer (arc)] -?> @MapContainer (arc) {{
        let bv = state.base_values();
        let maps: Vec<Renaming> = xs.map(|m| slot_map(bv, &m.data)).collect();
        Some(MapContainer::renaming(value_map(bv, find_mapping_total(&maps)?)))
    }});

    // Substitution needs both a read (to extract a term) and a
    // write (to add the substituted one), so it is registered as a
    // `FullPrim`: see `super::subst`. Its result is an
    // invocation, so it takes two names to read one -- the class and
    // the renaming placing it in `body`'s frame.
    // The two halves are called with the same arguments in one action, so
    // they share what one call computes.
    for half in [
        super::subst::Half::Class,
        super::subst::Half::Frame,
    ] {
        eg.add_full_primitive(
            super::subst::SlottedSubst {
                half,
                renaming: arc.clone(),
                slot: map.key(),
            },
            None,
        );
    }
}

#[rustfmt::skip]
pub(super) fn register_set(eg: &mut EGraph, set: &SetSort, arc: ArcSort, renaming: ArcSort) {
    add_primitive!(eg, "group-restrict" = {set.clone(): SetSort} |s: @SetContainer (arc.clone()), cs: @MapContainer (renaming.clone())| -?> @SetContainer (arc.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(intern_group(&mut state, group::restrict(&maps, &cs.data)))
    }});
    add_primitive!(eg, "group-close" = {set.clone(): SetSort} |s: @SetContainer (arc.clone())| -?> @SetContainer (arc.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(intern_group(&mut state, group::close(&maps)))
    }});
    add_primitive!(eg, "group-coset-reps" = {set.clone(): SetSort} |s: @SetContainer (arc.clone()), pinned: @MapContainer (renaming.clone())| -?> @SetContainer (arc.clone()) {{
        let values: Vec<Value> = s.data.iter().copied().collect();
        let maps = slot_maps(&state, values.iter().copied())?;
        let pinned = slot_map(state.base_values(), &pinned.data);
        let data = group::coset_reps(&maps, &pinned).into_iter().map(|i| values[i]).collect();
        Some(SetContainer { do_rebuild: false, data: Arc::new(data) })
    }});
    add_primitive!(eg, "coset-min" = {set.clone(): SetSort} |m: @MapContainer (renaming.clone()), s: @SetContainer (arc.clone())| -?> @MapContainer (renaming.clone()) {{
        let maps = slot_maps(&state, s.data.iter().copied())?;
        let m = slot_map(state.base_values(), &m.data);
        let least = group::coset_min(&m, &maps)?;
        Some(MapContainer::renaming(value_map(state.base_values(), least)))
    }});
    // `(root "p" cs grp)` and `(child "v" e cs grp)`: a binding whose reading of
    // its class is any element of the group, decided by the frame once the rest
    // of the pattern has pinned what it can (C5); see `Frame::refinements`.
    add_primitive!(eg, "root" = {set.clone(): SetSort} |v: S, cs: @MapContainer (renaming.clone()), grp: @SetContainer (arc.clone())| -?> Bd {{
        let group = slot_maps(&state, grp.data.iter().copied())?;
        let class_slots = slot_set(state.base_values(), &cs.data)?;
        Some(Bd::new(Binding::Root { var: PVarId::new(v.as_str()), class_slots, reading: Reading::Group(Arc::new(group)) }))
    }});
    add_primitive!(eg, "child" = {set.clone(): SetSort} |v: S, e: @MapContainer (renaming.clone()), cs: @MapContainer (renaming.clone()), grp: @SetContainer (arc.clone())| -?> Bd {{
        let group = slot_maps(&state, grp.data.iter().copied())?;
        let bv = state.base_values();
        Some(Bd::new(Binding::Child { var: PVarId::new(v.as_str()), edge: slot_map(bv, &e.data), class_slots: slot_set(bv, &cs.data)?, reading: Reading::Group(Arc::new(group)) }))
    }});
    add_primitive!(eg, "coset-same" = {set.clone(): SetSort} |m1: @MapContainer (renaming.clone()), m2: @MapContainer (renaming.clone()), s: @SetContainer (arc.clone())| -?> () {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        group::coset_same(&m1.data, &m2.data, &maps).then_some(())
    }});
    add_primitive!(eg, "group-slot-closure" = {set.clone(): SetSort} |s: @SetContainer (arc.clone()), slots: @MapContainer (renaming.clone())| -?> @MapContainer (renaming.clone()) {{
        let maps = value_maps(&state, s.data.iter().copied())?;
        Some(MapContainer::renaming(group::slot_closure(&maps, &slots.data)))
    }});

}

#[rustfmt::skip]
pub(super) fn register_vec(eg: &mut EGraph, vec: &VecSort, arc: ArcSort) {
    // `(shape e1 e2 ...)`: the edges in canonical spelling, then the renaming from
    // that spelling back to the node's names; see `shape`.
    add_primitive!(eg, "shape" = {vec.clone(): VecSort} [xs: # (vec.element())] -?> @VecContainer (arc) {{
        let maps = slot_maps(&state, xs)?;
        let data = register_renamings(&mut state, shape(&maps).into_maps());
        Some(VecContainer { do_rebuild: false, data })
    }});
}

#[rustfmt::skip]
pub(super) fn register_node_shape(eg: &mut EGraph, vec: &VecSort, arc: ArcSort, groups: ArcSort) {
    // `(node-shape (vec-of e1 ...) (vec-of g1 ...))`: the canonical edges, the
    // renaming back to the node's names, then its symmetries; see `node_shape`.
    add_primitive!(eg, "node-shape" = {vec.clone(): VecSort} |es: @VecContainer (arc.clone()), gs: @VecContainer (groups.clone())| -?> @VecContainer (arc.clone()) {{
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
pub(super) fn register_symmetries(eg: &mut EGraph, vec: &VecSort, arc: ArcSort, set: ArcSort) {
    // the symmetries `node-shape` put after its first `n` entries
    add_primitive!(eg, "symmetries-of" = {vec.clone(): VecSort} |xs: @VecContainer (arc.clone()), n: i64| -?> @SetContainer (set.clone()) {{
        let n = usize::try_from(n).ok()?;
        Some(SetContainer { do_rebuild: false, data: std::sync::Arc::new(xs.data.get(n..)?.iter().copied().collect()) })
    }});
}

#[rustfmt::skip]
pub(super) fn register_frame_vec(eg: &mut EGraph, vec: &VecSort, arc: ArcSort) {
    add_primitive!(eg, "refinements" = {vec.clone(): VecSort} |f: Fr| -> @VecContainer (arc) { VecContainer {
        do_rebuild: false,
        data: f
            .refinements()
            .into_iter()
            .map(|g| state.base_values().get::<Fr>(Fr::new(g)))
            .collect(),
    } });
}

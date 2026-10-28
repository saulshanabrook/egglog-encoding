//! Native values and primitives used by the slotted encoding.
use egglog::ast::{Literal, Span};
use egglog::constraint::{self, Constraint, TypeConstraint};
use egglog::prelude::*;
use egglog::sort::*;
use egglog::*;
use std::sync::Arc;

mod frame;
mod group;
mod primitives;
pub(crate) mod renaming;
mod subst;
pub(crate) mod terms;
mod types;
pub(crate) use frame::*;
pub(crate) use types::{Renaming, SlotSet};

fn map_container(data: std::collections::BTreeMap<Value, Value>) -> MapContainer {
    MapContainer::new(data, false, false)
}

/// Install the fixed runtime vocabulary once, before evaluating lowered code.
/// Ordinary egglog sorts and primitives are still used for the storage containers.
pub(super) fn register(eg: &mut EGraph) {
    add_base_sort(eg, NamesSort, span!()).unwrap();
    add_base_sort(eg, BindingSort, span!()).unwrap();
    add_base_sort(eg, FrameSort, span!()).unwrap();
    eg.parse_and_run_program(None, include_str!("sorts.egg"))
        .unwrap();
    let sort = |name| eg.type_info().get_sort_by_name(name).unwrap().clone();
    let [renaming, frames, group, groups, renamings] =
        ["Renaming", "Frames", "Group", "Groups", "Renamings"].map(sort);
    primitives::register_map(eg, renaming.clone());
    primitives::register_set(eg, group.clone(), renaming);
    primitives::register_frame_vec(eg, frames);
    primitives::register_vec(eg, renamings.clone());
    primitives::register_node_shape(eg, renamings.clone(), groups);
    primitives::register_symmetries(eg, renamings, group);
}

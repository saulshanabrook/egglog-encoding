//! Slotted matching and substitution, registered independently of generic containers.
use super::*;

mod frame;
mod group;
mod primitives;
mod renaming;
mod subst;
mod types;
pub use types::{Renaming, SlotSet};

pub use frame::*;
pub use subst::{SLOTTED_SUBST, SLOTTED_SUBST_FRAME};

pub(crate) fn register_base_sorts(eg: &mut EGraph) {
    add_base_sort(eg, NamesSort, span!()).unwrap();
    add_base_sort(eg, BindingSort, span!()).unwrap();
    add_base_sort(eg, FrameSort, span!()).unwrap();
}

fn is_renaming(sort: &ArcSort) -> bool {
    crate::prelude::container_sort_of::<MapSort>(sort)
        .is_some_and(|map| map.key().name() == "i64" && map.value().name() == "i64")
}

fn group_renaming(sort: &ArcSort) -> Option<ArcSort> {
    let set = crate::prelude::container_sort_of::<SetSort>(sort)?;
    is_renaming(&set.element()).then(|| set.element())
}

/// Register the overloads enabled by a newly declared sort. Each pair of vector
/// sorts is handled when its second member arrives, in either declaration order.
pub(crate) fn register_sort(eg: &mut EGraph, sort: &ArcSort) {
    if is_renaming(sort) {
        let map = crate::prelude::container_sort_of::<MapSort>(sort).unwrap();
        primitives::register_map(eg, map, sort.clone());
    } else if let Some(renaming) = group_renaming(sort) {
        let set = crate::prelude::container_sort_of::<SetSort>(sort).unwrap();
        primitives::register_set(eg, set, sort.clone(), renaming.clone());
        for edges in eg
            .type_info
            .get_arcsorts_by(|s| crate::prelude::container_sort_of::<VecSort>(s).is_some())
        {
            let vec = crate::prelude::container_sort_of::<VecSort>(&edges).unwrap();
            if vec.element().name() == renaming.name() {
                primitives::register_symmetries(eg, vec, edges.clone(), sort.clone());
            }
        }
    } else if let Some(vec) = crate::prelude::container_sort_of::<VecSort>(sort) {
        let element = vec.element();
        if element.name() == "Frame" {
            primitives::register_frame_vec(eg, vec, sort.clone());
        } else if is_renaming(&element) {
            primitives::register_vec(eg, vec, sort.clone());
            for set in eg
                .type_info
                .get_arcsorts_by(|s| crate::prelude::container_sort_of::<SetSort>(s).is_some())
            {
                if group_renaming(&set).is_some_and(|r| r.name() == element.name()) {
                    primitives::register_symmetries(eg, vec, sort.clone(), set);
                }
            }
            for groups in eg
                .type_info
                .get_arcsorts_by(|s| crate::prelude::container_sort_of::<VecSort>(s).is_some())
            {
                let inner = groups.inner_sorts();
                if group_renaming(&inner[0]).is_some_and(|r| r.name() == element.name()) {
                    primitives::register_node_shape(eg, vec, sort.clone(), groups);
                }
            }
        } else if let Some(renaming) = group_renaming(&element) {
            for edges in eg
                .type_info
                .get_arcsorts_by(|s| crate::prelude::container_sort_of::<VecSort>(s).is_some())
            {
                let other = crate::prelude::container_sort_of::<VecSort>(&edges).unwrap();
                if other.element().name() == renaming.name() {
                    primitives::register_node_shape(eg, other, edges.clone(), sort.clone());
                }
            }
        }
    }
}

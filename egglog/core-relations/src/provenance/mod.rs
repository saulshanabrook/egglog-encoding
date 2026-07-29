//! Compact execution-trace capture for backward slicing.
//!
//! Native commit paths append effective events to short-lived local batches
//! and publish them at existing engine barriers. The trace is causal evidence,
//! not a proof object; explanation, slicing, and replay are lazy cold consumers.

use std::{
    any::TypeId,
    sync::{
        Arc, Mutex, OnceLock, RwLock,
        atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering},
    },
};

use dashmap::mapref::entry::Entry;
use smallvec::SmallVec;

use crate::{
    AtomId, QueryEntry, TableId, Value, Variable,
    common::{DashMap, HashMap, HashSet},
    numeric_id::{DenseIdMap, NumericId},
};

mod capture;
mod model;
mod terms;

pub use capture::*;
pub use model::*;
pub use terms::*;

#[cfg(test)]
thread_local! {
    static TERM_PROJECTOR_FACT_EXPANSIONS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_term_projector_fact_expansions() {
    TERM_PROJECTOR_FACT_EXPANSIONS.set(0);
}

#[cfg(test)]
pub(crate) fn term_projector_fact_expansions() -> usize {
    TERM_PROJECTOR_FACT_EXPANSIONS.get()
}

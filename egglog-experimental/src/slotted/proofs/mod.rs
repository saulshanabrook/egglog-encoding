//! Surface proofs for slotted programs, their checker, and lifting from
//! encoded egglog proofs. See `egglog-experimental/src/slotted/PROOFS.md` for
//! the proof format and lifting rules.

mod bindings;
pub mod checker;
pub(super) mod context;
pub(super) mod coordinates;
pub mod format;
pub(super) mod guards;
mod lift_slots;
mod normal_form;
mod normalize;
pub(crate) mod pipeline;
mod program;
pub(super) mod resolve;
pub(in crate::slotted) mod runtime_substitution;
pub(super) mod substitution;
pub mod terms;

pub use checker::{SlottedCheckError, check_claim, check_proof};
pub use context::SourceError;
pub use format::{
    Claim, ClaimKind, ProofId, RulePremise, RuleProof, SlottedProof, SlottedProofStore,
};
pub use program::ResolvedSlottedProgram;
pub use resolve::resolve_program;
pub use terms::Renaming;

use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

pub(super) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub(super) type HashSet<K> = hashbrown::HashSet<K, BuildHasherDefault<FxHasher>>;

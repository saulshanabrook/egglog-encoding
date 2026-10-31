//! Surface proofs for slotted programs, their checker, and lifting from
//! encoded egglog proofs. See `egglog-experimental/src/slotted/PROOFS.md` for
//! the proof format and lifting rules.

pub mod checker;
mod coordinates;
pub mod format;
mod guards;
mod lift_slots;
mod normalize;
pub(crate) mod pipeline;
pub mod source;
pub mod terms;
mod unflatten;

pub use checker::{SlottedCheckError, check_claim, check_proof};
pub use format::{
    Claim, ClaimKind, ProofId, RulePremise, RuleProof, SlottedConclusion, SlottedProof,
    SlottedProofStore,
};
pub use source::{Constructor, SlottedProgram, SourceRule, Union};
pub use terms::Renaming;

use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;
type HashSet<K> = hashbrown::HashSet<K, BuildHasherDefault<FxHasher>>;

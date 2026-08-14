use std::sync::atomic::{AtomicU64, Ordering};

use crate::{ast::ResolvedVar, core::ResolvedCall};

pub(crate) type BuildHasher = std::hash::BuildHasherDefault<rustc_hash::FxHasher>;
pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasher>;
pub(crate) type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;
pub(crate) type HEntry<'a, A, B> = hashbrown::hash_map::Entry<'a, A, B, BuildHasher>;
pub type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasher>;
pub(crate) type IEntry<'a, A, B> = indexmap::map::Entry<'a, A, B>;
pub type IndexSet<K> = indexmap::IndexSet<K, BuildHasher>;

pub use egglog_ast::generic_ast_helpers::INTERNAL_SYMBOL_PREFIX;

static NEXT_SYMBOL_GEN_OWNER_ID: AtomicU64 = AtomicU64::new(1);

/// Generates fresh symbols for internal use during typechecking and flattening.
/// These are guaranteed not to collide with the
/// user's symbols because they use a reserved prefix.
#[derive(Debug)]
pub struct SymbolGen {
    hint_to_count: HashMap<String, usize>,
    reserved_string: String,
    leave_off_zero: bool,
    owner_id: u64,
    checkpoints: Vec<usize>,
    undo_log: Vec<SymbolGenUndo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SymbolGenUndo {
    hint: String,
    previous_count: Option<usize>,
}

/// An opaque marker for a [`SymbolGen`] transaction.
///
/// Markers must be committed or rolled back in last-in, first-out order.
#[must_use = "a symbol-generator checkpoint must be committed or rolled back"]
pub(crate) struct SymbolGenCheckpoint {
    owner_id: u64,
    depth: usize,
    undo_len: usize,
}

impl Clone for SymbolGen {
    fn clone(&self) -> Self {
        assert!(
            self.checkpoints.is_empty(),
            "cannot clone a SymbolGen with an active checkpoint"
        );
        debug_assert!(self.undo_log.is_empty());
        Self {
            hint_to_count: self.hint_to_count.clone(),
            reserved_string: self.reserved_string.clone(),
            leave_off_zero: self.leave_off_zero,
            owner_id: NEXT_SYMBOL_GEN_OWNER_ID.fetch_add(1, Ordering::Relaxed),
            checkpoints: Vec::new(),
            undo_log: Vec::new(),
        }
    }
}

impl PartialEq for SymbolGen {
    fn eq(&self, other: &Self) -> bool {
        self.hint_to_count == other.hint_to_count
            && self.reserved_string == other.reserved_string
            && self.leave_off_zero == other.leave_off_zero
            && self.checkpoints == other.checkpoints
            && self.undo_log == other.undo_log
    }
}

impl Eq for SymbolGen {}

impl SymbolGen {
    /// Create a new symbol generator with the given reserved prefix.
    pub fn new(reserved_string: String) -> Self {
        Self {
            hint_to_count: HashMap::default(),
            reserved_string,
            leave_off_zero: true,
            owner_id: NEXT_SYMBOL_GEN_OWNER_ID.fetch_add(1, Ordering::Relaxed),
            checkpoints: Vec::new(),
            undo_log: Vec::new(),
        }
    }

    /// Begin a transaction over fresh-name counters.
    ///
    /// Creating and committing an unchanged checkpoint are constant-time. A
    /// fresh-name mutation is journaled only while at least one checkpoint is
    /// active, so the ordinary non-transactional path retains a single map
    /// update.
    pub(crate) fn checkpoint(&mut self) -> SymbolGenCheckpoint {
        let checkpoint = SymbolGenCheckpoint {
            owner_id: self.owner_id,
            depth: self.checkpoints.len(),
            undo_len: self.undo_log.len(),
        };
        self.checkpoints.push(checkpoint.undo_len);
        checkpoint
    }

    /// Commit the most recently opened transaction.
    ///
    /// An inner transaction's journal remains available to an enclosing
    /// transaction. Committing the outermost transaction discards the journal.
    pub(crate) fn commit(&mut self, checkpoint: SymbolGenCheckpoint) {
        assert_eq!(
            self.owner_id, checkpoint.owner_id,
            "SymbolGen checkpoint belongs to a different generator"
        );
        assert_eq!(
            self.checkpoints.len(),
            checkpoint.depth + 1,
            "SymbolGen checkpoints must be committed in LIFO order"
        );
        assert_eq!(
            self.checkpoints.last().copied(),
            Some(checkpoint.undo_len),
            "SymbolGen checkpoint does not belong to the active transaction"
        );
        self.checkpoints.pop();
        if self.checkpoints.is_empty() {
            self.undo_log.clear();
        }
    }

    /// Roll back the most recently opened transaction exactly.
    pub(crate) fn rollback(&mut self, checkpoint: SymbolGenCheckpoint) {
        assert_eq!(
            self.owner_id, checkpoint.owner_id,
            "SymbolGen checkpoint belongs to a different generator"
        );
        assert_eq!(
            self.checkpoints.len(),
            checkpoint.depth + 1,
            "SymbolGen checkpoints must be rolled back in LIFO order"
        );
        assert_eq!(
            self.checkpoints.last().copied(),
            Some(checkpoint.undo_len),
            "SymbolGen checkpoint does not belong to the active transaction"
        );
        self.checkpoints.pop();
        while self.undo_log.len() > checkpoint.undo_len {
            let SymbolGenUndo {
                hint,
                previous_count,
            } = self.undo_log.pop().unwrap();
            match previous_count {
                Some(previous_count) => {
                    self.hint_to_count.insert(hint, previous_count);
                }
                None => {
                    self.hint_to_count.remove(&hint);
                }
            }
        }
    }

    /// Record and advance one hint counter, preserving its prior state when a
    /// surrounding transaction may need to roll the update back.
    fn next_count(&mut self, hint: String) -> usize {
        if !self.checkpoints.is_empty() {
            self.undo_log.push(SymbolGenUndo {
                previous_count: self.hint_to_count.get(&hint).copied(),
                hint: hint.clone(),
            });
        }
        let entry = self.hint_to_count.entry(hint).or_insert(0);
        let count = *entry;
        *entry += 1;
        count
    }

    /// By default, the first symbol generated with a given hint
    /// does not have a numeric suffix (e.g., "var" instead of "var0").
    /// This method changes that behavior.
    pub fn include_zero(&mut self, include: bool) {
        self.leave_off_zero = !include;
    }

    /// Check if this symbol generator has been used to generate any symbols.
    pub fn has_been_used(&self) -> bool {
        !self.hint_to_count.is_empty()
    }

    /// Get the reserved prefix used by this symbol generator.
    pub fn reserved_prefix(&self) -> &str {
        &self.reserved_string
    }

    /// Check if the given symbol is reserved (i.e., starts with the reserved prefix).
    pub fn is_reserved(&self, symbol: &str) -> bool {
        !self.reserved_string.is_empty() && symbol.starts_with(&self.reserved_string)
    }
}

/// This trait lets us statically dispatch between `fresh` methods for generic structs.
pub trait FreshGen<Head: ?Sized, Leaf> {
    fn fresh(&mut self, name_hint: &Head) -> Leaf;
}

impl FreshGen<str, String> for SymbolGen {
    fn fresh(&mut self, name_hint: &str) -> String {
        let count_before = self.next_count(name_hint.to_string());
        format!(
            "{}{}{}",
            self.reserved_string,
            name_hint,
            if self.leave_off_zero && count_before == 0 {
                "".to_string()
            } else {
                count_before.to_string()
            }
        )
    }
}

impl FreshGen<String, String> for SymbolGen {
    fn fresh(&mut self, name_hint: &String) -> String {
        self.fresh(name_hint.as_str())
    }
}

impl FreshGen<ResolvedCall, ResolvedVar> for SymbolGen {
    fn fresh(&mut self, name_hint: &ResolvedCall) -> ResolvedVar {
        let count = self.next_count(format!("{name_hint}"));
        let name = format!(
            "{}{}{}",
            self.reserved_string,
            name_hint,
            if self.leave_off_zero && count == 0 {
                "".to_string()
            } else {
                count.to_string()
            }
        );
        let sort = match name_hint {
            ResolvedCall::Func(f) => f.output().clone(),
            ResolvedCall::Primitive(prim) => prim.output().clone(),
            ResolvedCall::Values(sorts) => sorts[0].clone(),
        };
        ResolvedVar {
            name,
            sort,
            // fresh variables are never global references, since globals
            // are desugared away by `remove_globals`
            is_global_ref: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{FreshGen, SymbolGen};

    #[test]
    fn rollback_removes_new_hint() {
        let mut symbols = SymbolGen::new("__".to_owned());
        let checkpoint = symbols.checkpoint();
        assert_eq!(symbols.fresh("temporary"), "__temporary");
        symbols.rollback(checkpoint);

        assert_eq!(symbols.fresh("temporary"), "__temporary");
    }

    #[test]
    fn rollback_restores_existing_hint_count() {
        let mut symbols = SymbolGen::new("__".to_owned());
        assert_eq!(symbols.fresh("existing"), "__existing");
        let checkpoint = symbols.checkpoint();
        assert_eq!(symbols.fresh("existing"), "__existing1");
        assert_eq!(symbols.fresh("existing"), "__existing2");
        symbols.rollback(checkpoint);

        assert_eq!(symbols.fresh("existing"), "__existing1");
    }

    #[test]
    fn commit_preserves_generated_names() {
        let mut symbols = SymbolGen::new("__".to_owned());
        let checkpoint = symbols.checkpoint();
        assert_eq!(symbols.fresh("committed"), "__committed");
        symbols.commit(checkpoint);

        assert_eq!(symbols.fresh("committed"), "__committed1");
    }

    #[test]
    fn outer_rollback_undoes_committed_inner_checkpoint() {
        let mut symbols = SymbolGen::new("__".to_owned());
        let outer = symbols.checkpoint();
        assert_eq!(symbols.fresh("nested"), "__nested");
        let inner = symbols.checkpoint();
        assert_eq!(symbols.fresh("nested"), "__nested1");
        assert_eq!(symbols.fresh("inner"), "__inner");
        symbols.commit(inner);
        symbols.rollback(outer);

        assert_eq!(symbols.fresh("nested"), "__nested");
        assert_eq!(symbols.fresh("inner"), "__inner");
    }

    #[test]
    fn inner_rollback_preserves_outer_checkpoint_for_commit() {
        let mut symbols = SymbolGen::new("__".to_owned());
        let outer = symbols.checkpoint();
        assert_eq!(symbols.fresh("nested"), "__nested");
        let inner = symbols.checkpoint();
        assert_eq!(symbols.fresh("nested"), "__nested1");
        symbols.rollback(inner);
        assert_eq!(symbols.fresh("nested"), "__nested1");
        symbols.commit(outer);

        assert_eq!(symbols.fresh("nested"), "__nested2");
    }

    #[test]
    #[should_panic(expected = "SymbolGen checkpoints must be committed in LIFO order")]
    fn checkpoints_reject_out_of_order_commit() {
        let mut symbols = SymbolGen::new("__".to_owned());
        let outer = symbols.checkpoint();
        let _inner = symbols.checkpoint();
        symbols.commit(outer);
    }

    #[test]
    #[should_panic(expected = "cannot clone a SymbolGen with an active checkpoint")]
    fn clone_rejects_active_checkpoint() {
        let mut symbols = SymbolGen::new("__".to_owned());
        let _checkpoint = symbols.checkpoint();
        let _clone = symbols.clone();
    }

    #[test]
    #[should_panic(expected = "SymbolGen checkpoint belongs to a different generator")]
    fn checkpoint_rejects_a_different_generator() {
        let mut first = SymbolGen::new("__".to_owned());
        let checkpoint = first.checkpoint();
        let mut second = SymbolGen::new("__".to_owned());
        let _second_checkpoint = second.checkpoint();
        second.commit(checkpoint);
    }
}

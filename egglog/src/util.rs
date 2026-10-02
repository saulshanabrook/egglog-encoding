use crate::{ast::ResolvedVar, core::ResolvedCall};

pub(crate) type BuildHasher = std::hash::BuildHasherDefault<rustc_hash::FxHasher>;
pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasher>;
pub(crate) type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;
pub(crate) type HEntry<'a, A, B> = hashbrown::hash_map::Entry<'a, A, B, BuildHasher>;
pub type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasher>;
pub(crate) type IEntry<'a, A, B> = indexmap::map::Entry<'a, A, B>;
pub type IndexSet<K> = indexmap::IndexSet<K, BuildHasher>;

pub use egglog_ast::generic_ast_helpers::INTERNAL_SYMBOL_PREFIX;

/// Generates fresh symbols for internal use during typechecking and flattening.
/// These are guaranteed not to collide with the
/// user's symbols because they use a reserved prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolGen {
    hint_to_count: HashMap<String, usize>,
    /// Every symbol minted by this generator so far.
    ///
    /// `fresh` concatenates a hint with a per-hint counter, which by itself is
    /// *not* collision-free across different hints: e.g. minting for hint
    /// "n414" at count 11 and for hint "n4141" at count 1 both produce
    /// "n41411". Downstream passes treat resolved variables by name, so two
    /// distinct variables with the same name silently get conflated and
    /// corrupt action compilation. This set guarantees every minted symbol is
    /// unique, by advancing the per-hint counter past any name that has
    /// already been used.
    minted: HashSet<String>,
    reserved_string: String,
    leave_off_zero: bool,
}

impl SymbolGen {
    /// Create a new symbol generator with the given reserved prefix.
    pub fn new(reserved_string: String) -> Self {
        Self {
            hint_to_count: HashMap::default(),
            minted: HashSet::default(),
            reserved_string,
            leave_off_zero: true,
        }
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
        let entry = self.hint_to_count.entry(name_hint.to_string()).or_insert(0);
        let mut count = *entry;
        let name = loop {
            let candidate = format!(
                "{}{}{}",
                self.reserved_string,
                name_hint,
                if self.leave_off_zero && count == 0 {
                    "".to_string()
                } else {
                    count.to_string()
                }
            );
            // Advance past any name that has already been minted (possibly
            // via a different hint), so minted names are pairwise unique.
            if !self.minted.contains(&candidate) {
                break candidate;
            }
            count += 1;
        };
        *entry = count + 1;
        self.minted.insert(name.clone());
        name
    }
}

impl FreshGen<String, String> for SymbolGen {
    fn fresh(&mut self, name_hint: &String) -> String {
        self.fresh(name_hint.as_str())
    }
}

impl FreshGen<ResolvedCall, ResolvedVar> for SymbolGen {
    fn fresh(&mut self, name_hint: &ResolvedCall) -> ResolvedVar {
        let entry = self
            .hint_to_count
            .entry(format!("{name_hint}"))
            .or_insert(0);
        let mut count = *entry;
        let name = loop {
            let candidate = format!(
                "{}{}{}",
                self.reserved_string,
                name_hint,
                if self.leave_off_zero && count == 0 {
                    "".to_string()
                } else {
                    count.to_string()
                }
            );
            // Keep minted names pairwise unique; see the `str` impl.
            if !self.minted.contains(&candidate) {
                break candidate;
            }
            count += 1;
        };
        *entry = count + 1;
        self.minted.insert(name.clone());
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
    use super::*;
    use crate::{ast::FunctionSubtype, sort::EqSort, typechecking::FuncType};
    use std::sync::Arc;

    #[test]
    fn fresh_symbols_disambiguate_numeric_hints() {
        for hints in [["x1", "x", "x"], ["x", "x", "x1"]] {
            let mut symbols = SymbolGen::new("@".into());
            let names: HashSet<_> = hints.map(|hint| symbols.fresh(hint)).into_iter().collect();
            assert_eq!(names.len(), hints.len());
        }

        let mut symbols = SymbolGen::new("@".into());
        assert_eq!(symbols.fresh("x"), "@x");
        assert_eq!(symbols.fresh("x"), "@x1");
        assert_eq!(symbols.fresh("x"), "@x2");
    }

    #[test]
    fn typed_fresh_symbols_share_collision_checks() {
        let mut symbols = SymbolGen::new("@".into());
        let assumption = ResolvedCall::Func(Arc::new(FuncType {
            name: "reproduction_anchor_13".into(),
            subtype: FunctionSubtype::Custom,
            input: vec![],
            outputs: vec![Arc::new(EqSort {
                name: "Assumption".into(),
            })],
        }));
        let type_anchor = ResolvedCall::Func(Arc::new(FuncType {
            name: "reproduction_anchor_133".into(),
            subtype: FunctionSubtype::Custom,
            input: vec![],
            outputs: vec![Arc::new(EqSort {
                name: "Type".into(),
            })],
        }));
        let mut names = HashSet::default();
        for _ in 0..35 {
            let var = symbols.fresh(&assumption);
            assert_eq!(var.sort.name(), "Assumption");
            assert!(names.insert(var.name));
        }
        for _ in 0..5 {
            let var = symbols.fresh(&type_anchor);
            assert_eq!(var.sort.name(), "Type");
            assert!(names.insert(var.name));
        }
        assert!(names.insert(symbols.fresh("reproduction_anchor_1334")));
    }

    #[test]
    fn cloned_generator_keeps_allocations_with_zero_suffixes() {
        let mut symbols = SymbolGen::new("@".into());
        symbols.include_zero(true);
        assert_eq!(symbols.fresh("x"), "@x0");
        assert_eq!(symbols.fresh("x0"), "@x00");

        let mut snapshot = symbols.clone();
        snapshot.include_zero(false);
        assert_eq!(snapshot.fresh("x00"), "@x001");
        assert_eq!(symbols.fresh("x"), snapshot.fresh("x"));
    }
}

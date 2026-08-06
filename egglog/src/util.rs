use crate::{
    ast::{ResolvedBindingId, ResolvedVar, ResolvedVarBinding},
    core::ResolvedCall,
    typechecking::{FunctionRegistrationId, IndexRegistrationId},
};

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
    generated_symbols: HashSet<String>,
    reserved_string: String,
    leave_off_zero: bool,
    // Callable identities share SymbolGen's push/pop high-water lifetime. The
    // e-graph preserves this generator across pop, so a later declaration can
    // never reuse an identity held by a resolved command from the popped scope.
    next_function_registration_id: u32,
    next_index_registration_id: u32,
    next_resolved_binding_id: u32,
}

impl SymbolGen {
    /// Create a new symbol generator with the given reserved prefix.
    pub fn new(reserved_string: String) -> Self {
        Self {
            hint_to_count: HashMap::default(),
            generated_symbols: HashSet::default(),
            reserved_string,
            leave_off_zero: true,
            next_function_registration_id: 0,
            next_index_registration_id: 0,
            next_resolved_binding_id: 0,
        }
    }

    pub(crate) fn fresh_function_registration_id(&mut self) -> FunctionRegistrationId {
        let identity = FunctionRegistrationId::new(self.next_function_registration_id);
        self.next_function_registration_id = self
            .next_function_registration_id
            .checked_add(1)
            .expect("function registration identity space exhausted");
        identity
    }

    pub(crate) fn fresh_index_registration_id(&mut self) -> IndexRegistrationId {
        let identity = IndexRegistrationId::new(self.next_index_registration_id);
        self.next_index_registration_id = self
            .next_index_registration_id
            .checked_add(1)
            .expect("index registration identity space exhausted");
        identity
    }

    pub(crate) fn fresh_resolved_binding_id(&mut self) -> ResolvedBindingId {
        let identity = ResolvedBindingId::new(self.next_resolved_binding_id);
        self.next_resolved_binding_id = self
            .next_resolved_binding_id
            .checked_add(1)
            .expect("resolved binding identity space exhausted");
        identity
    }

    /// Advance this generator past an exact binding already present in IR that
    /// was produced by another frontend-owned generator.
    pub(crate) fn observe_resolved_binding_id(&mut self, identity: ResolvedBindingId) {
        let next = identity
            .ordinal()
            .checked_add(1)
            .expect("resolved binding identity space exhausted");
        self.next_resolved_binding_id = self.next_resolved_binding_id.max(next);
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
        loop {
            let entry = self.hint_to_count.entry(name_hint.to_string()).or_insert(0);
            let count_before = *entry;
            *entry += 1;
            let candidate = format!(
                "{}{}{}",
                self.reserved_string,
                name_hint,
                if self.leave_off_zero && count_before == 0 {
                    "".to_string()
                } else {
                    count_before.to_string()
                }
            );
            if self.generated_symbols.insert(candidate.clone()) {
                return candidate;
            }
        }
    }
}

impl FreshGen<String, String> for SymbolGen {
    fn fresh(&mut self, name_hint: &String) -> String {
        self.fresh(name_hint.as_str())
    }
}

impl FreshGen<ResolvedCall, ResolvedVar> for SymbolGen {
    fn fresh(&mut self, name_hint: &ResolvedCall) -> ResolvedVar {
        let name = self.fresh(&format!("{name_hint}"));
        let sort = match name_hint {
            ResolvedCall::Func(f) => f.output().clone(),
            ResolvedCall::Primitive(prim) => prim.output().clone(),
            ResolvedCall::Values(sorts) => sorts[0].clone(),
        };
        ResolvedVar {
            name,
            sort,
            binding: ResolvedVarBinding::Lexical {
                id: self.fresh_resolved_binding_id(),
            },
            // fresh variables are never global references, since globals
            // are desugared away by `remove_globals`
            is_global_ref: false,
        }
    }
}

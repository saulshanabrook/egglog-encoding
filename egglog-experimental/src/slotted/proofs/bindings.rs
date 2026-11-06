use egglog::util::{FreshGen, INTERNAL_SYMBOL_PREFIX, SymbolGen};
use std::collections::{BTreeMap, BTreeSet};

/// Distinct names for captured globals and locals in string-keyed substitutions.
pub(super) struct GlobalNames {
    pub aliases: BTreeMap<String, String>,
    pub symbols: SymbolGen,
}

impl GlobalNames {
    pub fn new<'a>(
        globals: impl IntoIterator<Item = &'a String>,
        locals: &BTreeSet<String>,
        used: impl IntoIterator<Item = String>,
    ) -> Self {
        let globals: Vec<_> = globals.into_iter().collect();
        let used: BTreeSet<_> = used
            .into_iter()
            .chain(globals.iter().map(|name| (*name).clone()))
            .collect();
        let mut prefix = format!("{INTERNAL_SYMBOL_PREFIX}slotted-resolve-");
        while used.iter().any(|name| name.starts_with(&prefix)) {
            prefix.push('-');
        }
        let mut symbols = SymbolGen::new(prefix);
        let aliases = globals
            .into_iter()
            .map(|name| {
                let alias = if locals.contains(name) {
                    symbols.fresh(format!("captured-{name}").as_str())
                } else {
                    name.clone()
                };
                (name.clone(), alias)
            })
            .collect();
        Self { aliases, symbols }
    }
}

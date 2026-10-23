//! Source slot names are interned independently of e-class and global names.
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
pub(super) struct Slots {
    names: BTreeMap<String, i64>,
    used: BTreeSet<i64>,
    next: i64,
}

impl Default for Slots {
    fn default() -> Self {
        Self {
            names: BTreeMap::new(),
            used: BTreeSet::new(),
            next: i64::MIN,
        }
    }
}

impl Slots {
    pub fn intern(&mut self, source: &str) -> Result<String, String> {
        let name = source.strip_prefix('$').ok_or("expected a slot literal")?;
        let numeric = name.strip_prefix(['+', '-']).unwrap_or(name);
        let number = if !numeric.is_empty() && numeric.bytes().all(|c| c.is_ascii_digit()) {
            Some(
                name.parse::<i64>()
                    .map_err(|_| format!("slot {source} is outside the signed 64-bit range"))?,
            )
        } else {
            if name.is_empty() || !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
                return Err(format!("invalid slot literal {source}"));
            }
            None
        };
        let key = format!(
            "${}",
            number.map_or_else(|| name.to_owned(), |n| n.to_string())
        );
        if self.names.contains_key(&key) {
            return Ok(key);
        }
        // Preserve numeric IDs when available, including for existing encoded
        // fixtures. Later numeric names cannot alias an earlier named slot.
        let id = if let Some(n) = number.filter(|n| !self.used.contains(n)) {
            n
        } else {
            while self.used.contains(&self.next) {
                self.next = self.next.checked_add(1).ok_or("too many slot names")?;
            }
            self.next
        };
        self.used.insert(id);
        self.names.insert(key.clone(), id);
        Ok(key)
    }

    pub fn id(&self, name: &str) -> i64 {
        self.names[name]
    }
}

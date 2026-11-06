use super::SlotMap;

/// `a ∘ b`: `b` applies first; undefined wherever either step is.
pub(super) fn compose(a: &SlotMap, b: &SlotMap) -> SlotMap {
    b.iter()
        .filter_map(|(x, y)| a.get(y).map(|z| (*x, *z)))
        .collect()
}

pub(super) fn inverse(a: &SlotMap) -> SlotMap {
    a.iter().map(|(k, v)| (*v, *k)).collect()
}

pub(super) fn is_identity(g: &SlotMap) -> bool {
    g.iter().all(|(k, v)| k == v)
}

pub(super) fn slot_map_string(g: &SlotMap) -> String {
    let entries: Vec<String> = g.iter().map(|(k, v)| format!("{k}->{v}")).collect();
    format!("{{{}}}", entries.join(", "))
}

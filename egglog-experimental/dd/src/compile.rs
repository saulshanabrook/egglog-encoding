//! Rule IR and row representation for the DD backend.
//!
//! ## Row representation
//!
//! Every relation's rows are stored in the Rust-side mirror as a variable-width
//! boxed slice of `u32` (egglog [`Value`] reps), exactly `arity` columns wide.
//! `lookup_id` / `for_each` / `table_size` read the mirror.

use egglog_backend_trait::{ExternalFunctionId, FunctionId, QueryEntry, Value};

/// Upper bound on relation arity (sanity check; the mirror row is
/// variable-width, so this is generous).
pub const MAX_ARITY: usize = 64;

/// Uniform mirror row type: a variable-width boxed slice of `u32`
/// (egglog `Value` reps), exactly `arity` columns wide.
pub type Row = Box<[u32]>;

/// How a function resolves a functional-dependency conflict (two rows sharing
/// the same key columns with different output columns). Recognized from the
/// trait `MergeFn` (see `lib.rs::add_table`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MergeMode {
    /// Plain relation: the whole row is the key, no output column to resolve.
    Relation,
    /// `:merge old` / `AssertEq`: keep the existing value on conflict.
    Old,
    /// `:merge new`: keep the new value on conflict.
    New,
    /// `:merge (ordering-min old new)` / `UnionId`: keep the numerically
    /// smallest value (the union-find leader).
    Min,
    /// A merge that COMPUTES the surviving value rather than selecting one — a
    /// primitive like `(or old new)` or a constructor like `(C2 old new)`. The
    /// retained [`MergeTree`] (in `RelationInfo::merge_tree`) is evaluated
    /// host-side to fold conflicting values.
    Computed,
}

/// A retained, evaluatable `:merge` expression tree (the `MergeMode::Computed`
/// case), translated from the trait `MergeFn` at `add_table`. `Old`/`New` read
/// the two conflicting output values being folded.
#[derive(Clone, Debug)]
pub enum MergeTree {
    /// The accumulated ("old") output value.
    Old,
    /// The incoming ("new") output value.
    New,
    /// A constant.
    Const(u32),
    /// Apply a primitive to the evaluated arguments (e.g. `or` / `max` / `+`).
    Prim(ExternalFunctionId, Vec<MergeTree>),
    /// Look up (hash-cons / mint on miss) a constructor e-node from the evaluated
    /// argument eclasses (e.g. a merge that builds `(C2 old new)`).
    Func(FunctionId, Vec<MergeTree>),
}

/// Pack a slice of `Value`s into a [`Row`] (exactly `vals.len()` columns).
pub fn pack_row(vals: &[Value]) -> Row {
    use egglog_numeric_id::NumericId;
    assert!(
        vals.len() <= MAX_ARITY,
        "row arity {} exceeds {MAX_ARITY}",
        vals.len()
    );
    vals.iter().map(|v| v.rep()).collect()
}

/// Read column `i` (0-based) out of a [`Row`].
#[inline]
pub fn row_col(r: &Row, i: usize) -> u32 {
    r[i]
}

/// Unpack the first `arity` columns of a [`Row`] into a `Vec<Value>`.
pub fn unpack_row(r: &Row, arity: usize) -> Vec<Value> {
    use egglog_numeric_id::NumericId;
    (0..arity).map(|i| Value::new(row_col(r, i))).collect()
}

/// One column reference in a rule body atom or head action: either a bound
/// variable (identified by its [`egglog_backend_trait::VariableId`] rep) or a
/// constant value.
#[derive(Clone, Debug)]
pub enum Slot {
    Var(u32),
    Const(u32),
}

/// Resolve a [`Slot`] to a concrete `u32` value: a constant resolves to itself,
/// a variable resolves through `get` (the current binding env), or `None` if the
/// variable is unbound.
pub fn slot_lookup(s: &Slot, get: &dyn Fn(u32) -> Option<u32>) -> Option<u32> {
    match s {
        Slot::Var(v) => get(*v),
        Slot::Const(c) => Some(*c),
    }
}

impl Slot {
    pub fn from_entry(e: &QueryEntry) -> Self {
        use egglog_numeric_id::NumericId;
        match e {
            QueryEntry::Var(v) => Slot::Var(v.id.rep()),
            QueryEntry::Const { val, .. } => Slot::Const(val.rep()),
        }
    }
}

/// Which row-subsumption view a body atom reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReadMode {
    /// Ordinary user/body matching: live rows only.
    Live,
    /// Internal subsumption scan: subsumed rows only.
    Subsumed,
    /// Internal maintenance scan: live and subsumed rows.
    All,
}

impl ReadMode {
    pub fn from_filter(is_subsumed: Option<bool>) -> Self {
        match is_subsumed {
            Some(false) => ReadMode::Live,
            Some(true) => ReadMode::Subsumed,
            None => ReadMode::All,
        }
    }
}

/// A distinct DD input stream. The same logical relation can be read through
/// multiple subsumption views in one fused ruleset, and those views must not be
/// collapsed to one input.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReadKey {
    pub func: FunctionId,
    pub mode: ReadMode,
}

/// A body atom: a function table reference with one [`Slot`] per column.
#[derive(Clone, Debug)]
pub struct BodyAtom {
    pub func: FunctionId,
    pub slots: Vec<Slot>,
    /// Subsumption filter for this atom (from `query_table`): `Some(false)`
    /// excludes subsumed rows (the default for user queries), `None` includes all
    /// rows (the term encoder's `:internal-include-subsumed` congruence/rebuild
    /// rules, which must see subsumed rows to canonicalize them).
    pub read_mode: ReadMode,
}

impl BodyAtom {
    pub fn from_entries(
        func: FunctionId,
        entries: &[QueryEntry],
        is_subsumed: Option<bool>,
    ) -> Self {
        BodyAtom {
            func,
            slots: entries.iter().map(Slot::from_entry).collect(),
            read_mode: ReadMode::from_filter(is_subsumed),
        }
    }

    pub fn read_key(&self) -> ReadKey {
        ReadKey {
            func: self.func,
            mode: self.read_mode,
        }
    }
}

/// One operation in a rule **body**, in emission order.
#[derive(Clone, Debug)]
pub enum BodyOp {
    /// Match a table/relation atom.
    Atom(BodyAtom),
    /// Evaluate a primitive `func(args..)` — a `!=` guard or value-computing
    /// prim, applied host-side over the DD join's bindings.
    Prim {
        id: ExternalFunctionId,
        args: Vec<Slot>,
        ret: Slot,
    },
}

/// One operation in a rule **head**, in emission order.
#[derive(Clone, Debug)]
pub enum HeadOp {
    /// `(set func(key..) = val)` / relation `insert` — slots are the full row.
    Set { func: FunctionId, slots: Vec<Slot> },
    /// `(delete func(key..))` — retraction.
    Remove { func: FunctionId, slots: Vec<Slot> },
    /// `(subsume func(key..))`.
    Subsume { func: FunctionId, slots: Vec<Slot> },
    /// RHS function lookup binding `ret` (eq-sort constructor: create on miss).
    Lookup {
        func: FunctionId,
        args: Vec<Slot>,
        ret: u32,
    },
    /// RHS primitive call binding `ret`.
    Call {
        id: ExternalFunctionId,
        args: Vec<Slot>,
        ret: u32,
    },
    /// `(union l r)`.
    Union { l: Slot, r: Slot },
    /// `(panic msg)`.
    Panic(String),
}

/// The compiled IR for one egglog rule.
///
/// `body` is an ordered list of table-atom matches and primitive evaluations;
/// `head` is an ordered list of writes. `run_rules` runs the body table-atom
/// join on the DD dataflow, then applies body primitives and head
/// actions host-side (see [`crate::interpret`]).
#[derive(Clone, Debug, Default)]
pub struct RuleIr {
    pub name: String,
    pub body: Vec<BodyOp>,
    pub head: Vec<HeadOp>,
}

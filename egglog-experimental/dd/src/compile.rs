//! Rule IR and row representation for the DD backend.
//!
//! ## Row representation
//!
//! Every relation's rows are stored in the Rust-side mirror as a variable-width
//! boxed slice of `u32` (egglog [`Value`] reps), exactly `arity` columns wide.
//! `lookup_id` / `for_each` / `table_size` read the mirror.

use egglog_backend_trait::{ExternalFunctionId, FunctionId, QueryEntry};

/// Upper bound on relation arity (sanity check; the mirror row is
/// variable-width, so this is generous).
pub const MAX_ARITY: usize = 64;

/// Uniform mirror row type: a variable-width boxed slice of `u32`
/// (egglog `Value` reps), exactly `arity` columns wide.
pub type Row = Box<[u32]>;

/// How a function resolves a functional-dependency conflict (two rows sharing
/// the same key columns with different output columns). Recognized from the
/// trait `MergeFn` (see `lib.rs::add_table`).
///
/// The common modes intentionally do not all go through [`MergeTree`]. A
/// relation has no output to merge, while top-level `Old`, `New`, and `Min`
/// select a value without cloning or evaluating a tree and without requiring a
/// mutable primitive/hash-cons context. Only a merge that actually evaluates an
/// expression uses `Computed`. [`MergeTree::Old`] and [`MergeTree::New`] still
/// exist because those operands can occur inside a larger computed expression.
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
    /// A native `(union l r)`. Term encoding normally lowers this to `@uf`
    /// writes; the interpreter returns an error if this operation reaches it.
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
///
/// This backend-local IR is retained deliberately.
/// [`egglog_backend_trait::RuleBuilderOps`] supplies a rule as a sequence of
/// callbacks before the backend knows which rules will be run together. DD
/// cannot construct the fused ruleset dataflow until `run_rules` provides that
/// membership, and the host still needs the primitive and head operations after
/// DD returns bindings. Lowering each callback or rule directly would either
/// lose ruleset-wide input/arrangement sharing or retain equivalent metadata
/// elsewhere.
#[derive(Clone, Debug, Default)]
pub struct RuleIr {
    pub name: String,
    pub body: Vec<BodyOp>,
    pub head: Vec<HeadOp>,
}

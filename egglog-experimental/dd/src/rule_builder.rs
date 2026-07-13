//! `impl RuleBuilderOps` for the Differential Dataflow backend.
//!
//! An **accumulator**: each `RuleBuilderOps` call appends to an in-progress
//! [`RuleIr`] (defined in `compile.rs`) in emission order, and `build()`
//! registers it on the egraph. The backend must retain this representation until
//! `run_rules` reveals ruleset membership, when [`crate::dd_native`] can build a
//! fused join and [`crate::interpret`] can execute the host-side operations.

use anyhow::Result;
use egglog_backend_trait::{
    Backend, BaseValues, ColumnTy, ExternalFunctionId, FunctionId, PanicMsg, QueryEntry,
    RuleBuilderOps, RuleId, Variable,
};
use egglog_numeric_id::NumericId;

use crate::compile::{BodyAtom, BodyOp, HeadOp, ReadMode, RuleIr, Slot};
use crate::EGraph;

/// Accumulates a rule's body ops and head ops, then registers them.
pub struct DdRuleBuilder<'a> {
    egraph: &'a mut EGraph,
    ir: RuleIr,
    /// Fresh variable counter, seeded above any caller-provided variable id.
    next_var: u32,
}

impl<'a> DdRuleBuilder<'a> {
    pub fn new(egraph: &'a mut EGraph, desc: &str) -> Self {
        DdRuleBuilder {
            egraph,
            ir: RuleIr {
                name: desc.to_string(),
                ..RuleIr::default()
            },
            next_var: 1 << 24, // keep builder-synthesized vars away from caller ids
        }
    }

    fn fresh_var(&mut self, name: Option<&str>) -> QueryEntry {
        let rep = self.next_var;
        self.next_var += 1;
        QueryEntry::Var(Variable {
            // `VariableId` is not re-exported by the backend trait; the target
            // type is inferred from the `id` field so `NumericId::new` mints it
            // without naming the type.
            id: NumericId::new(rep),
            name: name.map(|s| s.to_string().into_boxed_str()),
        })
    }
}

impl<'a> RuleBuilderOps for DdRuleBuilder<'a> {
    fn new_var(&mut self, _ty: ColumnTy) -> QueryEntry {
        self.fresh_var(None)
    }

    fn new_var_named(&mut self, _ty: ColumnTy, name: &str) -> QueryEntry {
        self.fresh_var(Some(name))
    }

    fn base_values(&self) -> &BaseValues {
        self.egraph.db.base_values()
    }

    fn query_table(
        &mut self,
        func: FunctionId,
        entries: &[QueryEntry],
        is_subsumed: Option<bool>,
    ) -> Result<()> {
        let atom = BodyAtom {
            func,
            slots: entries.iter().map(Slot::from_entry).collect(),
            read_mode: match is_subsumed {
                Some(false) => ReadMode::Live,
                Some(true) => ReadMode::Subsumed,
                None => ReadMode::All,
            },
        };
        self.ir.body.push(BodyOp::Atom(atom));
        Ok(())
    }

    fn query_prim(
        &mut self,
        func: ExternalFunctionId,
        entries: &[QueryEntry],
        _ret_ty: ColumnTy,
    ) -> Result<()> {
        if entries.is_empty() {
            return Err(anyhow::anyhow!("DD backend: query_prim with no entries"));
        }
        let args: Vec<Slot> = entries[..entries.len() - 1]
            .iter()
            .map(Slot::from_entry)
            .collect();
        let ret = Slot::from_entry(entries.last().unwrap());
        self.ir.body.push(BodyOp::Prim {
            id: func,
            args,
            ret,
        });
        Ok(())
    }

    fn call_external_func(
        &mut self,
        func: ExternalFunctionId,
        args: &[QueryEntry],
        _ret_ty: ColumnTy,
        _panic_msg: PanicMsg,
    ) -> QueryEntry {
        let ret = self.fresh_var(None);
        let QueryEntry::Var(Variable { id, .. }) = &ret else {
            unreachable!()
        };
        let rid = id.rep();
        let slots: Vec<Slot> = args.iter().map(Slot::from_entry).collect();
        self.ir.head.push(HeadOp::Call {
            id: func,
            args: slots,
            ret: rid,
        });
        ret
    }

    fn lookup(
        &mut self,
        func: FunctionId,
        entries: &[QueryEntry],
        _panic_msg: PanicMsg,
    ) -> QueryEntry {
        let ret = self.fresh_var(None);
        let QueryEntry::Var(Variable { id, .. }) = &ret else {
            unreachable!()
        };
        let rid = id.rep();
        let args: Vec<Slot> = entries.iter().map(Slot::from_entry).collect();
        self.ir.head.push(HeadOp::Lookup {
            func,
            args,
            ret: rid,
        });
        ret
    }

    fn subsume(&mut self, func: FunctionId, entries: &[QueryEntry]) -> Result<()> {
        let slots: Vec<Slot> = entries.iter().map(Slot::from_entry).collect();
        self.ir.head.push(HeadOp::Subsume { func, slots });
        Ok(())
    }

    fn set(&mut self, func: FunctionId, entries: &[QueryEntry]) {
        let slots: Vec<Slot> = entries.iter().map(Slot::from_entry).collect();
        self.ir.head.push(HeadOp::Set { func, slots });
    }

    fn remove(&mut self, func: FunctionId, entries: &[QueryEntry]) {
        let slots: Vec<Slot> = entries.iter().map(Slot::from_entry).collect();
        self.ir.head.push(HeadOp::Remove { func, slots });
    }

    fn union(&mut self, l: QueryEntry, r: QueryEntry) {
        self.ir.head.push(HeadOp::Union {
            l: Slot::from_entry(&l),
            r: Slot::from_entry(&r),
        });
    }

    fn panic(&mut self, message: String) {
        self.ir.head.push(HeadOp::Panic(message));
    }

    fn new_panic(&mut self, message: String) -> ExternalFunctionId {
        Backend::new_panic(self.egraph, message)
    }

    fn free_external_func(&mut self, func: ExternalFunctionId) {
        Backend::free_external_func(self.egraph, func);
    }

    fn build(self: Box<Self>) -> Result<RuleId> {
        let this = *self;
        let id = RuleId::new(this.egraph.rules.len() as u32);
        this.egraph.rules.push(Some(this.ir));
        Ok(id)
    }
}

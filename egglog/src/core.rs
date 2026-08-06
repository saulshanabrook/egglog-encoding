//! This file implements the core IR of the language, which is called CoreRule.
//! CoreRule uses a conjunctive query-like IR for the body (queries) and a
//! SSA-like IR for the head (actions) based on the previous CoreAction form.
//! Every construct has two forms: a standard (unresolved) form and a resolved form,
//! which differs in whether the head is a symbol or a resolved call.
//! Currently, CoreRule has several usages:
//!   Typechecking is done over CoreRule format
//!   Canonicalization is done over CoreRule format
//!   ActionCompilers further compiles core actions to programs in a small VM
//!   GJ compiler further compiler core queries to gj's CompiledQueries
//!
//! Most compiler-time optimizations are expected to be done over CoreRule format.
use std::hash::Hasher;
use std::marker::PhantomData;

use crate::{
    constraint::{AtomConstraints, grounded_check},
    *,
};
pub use egglog_ast::core::{
    GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
};
use egglog_ast::generic_ast::{GenericAction, GenericActions, GenericExpr};
use egglog_ast::span::Span;
use typechecking::{
    FrontendAuthority, FuncType, PrimitiveAuthority, PrimitiveRegistrationId, PrimitiveValidator,
    PrimitiveWithId, SortRegistrationId, TypeError,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HeadOrEq<Head> {
    Head(Head),
    Eq,
}

pub(crate) type StringOrEq = HeadOrEq<String>;
pub type AtomTerm = GenericAtomTerm<String>;
pub type Atom<Head> = GenericAtom<Head, String>;
pub type CoreAction = GenericCoreAction<String, String>;

impl From<String> for StringOrEq {
    fn from(value: String) -> Self {
        StringOrEq::Head(value)
    }
}

impl<Head> HeadOrEq<Head> {
    pub fn is_eq(&self) -> bool {
        matches!(self, HeadOrEq::Eq)
    }
}

#[derive(Debug, Clone)]
pub struct SpecializedPrimitive {
    prim_with_id: PrimitiveWithId,
    registration_authority: FrontendAuthority<PrimitiveRegistrationId>,
    input: Vec<ArcSort>,
    input_identities: Vec<SortRegistrationId>,
    input_authorities: Vec<FrontendAuthority<SortRegistrationId>>,
    output: ArcSort,
    output_identity: SortRegistrationId,
    output_authority: FrontendAuthority<SortRegistrationId>,
}

impl SpecializedPrimitive {
    fn new(
        prim_with_id: PrimitiveWithId,
        input: Vec<ArcSort>,
        output: ArcSort,
        typeinfo: &TypeInfo,
    ) -> Self {
        let input_identities = input
            .iter()
            .map(|sort| typeinfo.expect_sort_registration_id(sort))
            .collect::<Vec<_>>();
        let input_authorities = input_identities
            .iter()
            .map(|identity| typeinfo.sort_authority(*identity))
            .collect();
        let output_identity = typeinfo.expect_sort_registration_id(&output);
        let output_authority = typeinfo.sort_authority(output_identity);
        let registration_authority = prim_with_id.registration_authority();
        Self {
            prim_with_id,
            registration_authority,
            input,
            input_identities,
            input_authorities,
            output,
            output_identity,
            output_authority,
        }
    }

    /// Get the name of this primitive
    pub fn name(&self) -> &str {
        self.prim_with_id.primitive.name()
    }

    /// Get the output sort of this primitive
    pub fn output(&self) -> &ArcSort {
        &self.output
    }

    /// Get the input sorts of this primitive
    pub fn input(&self) -> &[ArcSort] {
        &self.input
    }

    #[allow(dead_code)] // consumed by the standalone snapshot mapper
    pub(crate) fn input_identities(&self) -> &[SortRegistrationId] {
        &self.input_identities
    }

    #[allow(dead_code)] // consumed by the standalone snapshot mapper
    pub(crate) fn output_identity(&self) -> SortRegistrationId {
        self.output_identity
    }

    /// Get the frontend-owned identity of this primitive registration.
    #[allow(dead_code)] // consumed by the standalone snapshot mapper
    pub(crate) fn registration_id(&self) -> PrimitiveRegistrationId {
        self.prim_with_id.registration_id()
    }

    /// Get the semantics declared by this primitive's registration site.
    #[allow(dead_code)]
    pub(crate) fn authority(&self) -> &PrimitiveAuthority {
        self.prim_with_id.authority()
    }

    /// Get the external function ID of this primitive
    pub(crate) fn external_id(&self, ctx: crate::Context) -> ExternalFunctionId {
        self.prim_with_id.context_ids[ctx].unwrap_or_else(|| {
            panic!(
                "primitive {:?} is not valid in context {ctx:?}",
                self.prim_with_id.primitive.name()
            )
        })
    }

    /// Get the validator function of this primitive, if any
    pub fn validator(&self) -> Option<&PrimitiveValidator> {
        self.prim_with_id.validator.as_ref()
    }
}

impl PartialEq for SpecializedPrimitive {
    fn eq(&self, other: &Self) -> bool {
        // This is the key used when resolved atoms are deduplicated by
        // `(head, inputs)`. The frontend registration ID identifies the
        // primitive definition without making backend callback tokens part of
        // resolved-program identity. The concrete input/output sorts identify
        // the specialization of generic primitives. The primitive name and
        // validator are registration metadata, so they are intentionally not
        // separate key fields.
        self.registration_authority == other.registration_authority
            && self.output_authority == other.output_authority
            && self.input_authorities == other.input_authorities
    }
}

impl Eq for SpecializedPrimitive {}

impl Hash for SpecializedPrimitive {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.registration_authority.hash(state);
        self.output_authority.hash(state);
        self.input_authorities.hash(state);
    }
}

/// A resolved call in one frontend view.
///
/// `Func` ordinals and `Values` pointers are local-catalog keys only. Portable
/// snapshot mapping consumes each view separately and qualifies those keys;
/// callers must not compare raw calls from independent catalogs. Primitive
/// specializations carry their deterministic view discriminator explicitly
/// because proof instrumentation compares those keys across sibling views.
#[derive(Debug, Clone)]
pub enum ResolvedCall {
    Func(FuncType),
    Primitive(SpecializedPrimitive),
    /// The `values` tuple constructor, used to destructure a tuple-output function's outputs in a
    /// query (`(= (values a b) (f x))`) or to construct them in a `set` action
    /// (`(set (f x) (values a b))`). Carries the output sorts. It never reaches the backend on its
    /// own: it is always paired with a tuple-output function call when lowering to core.
    Values(Vec<ArcSort>),
}

impl PartialEq for ResolvedCall {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ResolvedCall::Func(a), ResolvedCall::Func(b)) => a == b,
            (ResolvedCall::Primitive(a), ResolvedCall::Primitive(b)) => a == b,
            (ResolvedCall::Values(a), ResolvedCall::Values(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b)
                        .all(|(left, right)| Arc::ptr_eq(left, right))
            }
            _ => false,
        }
    }
}

impl Eq for ResolvedCall {}

impl Hash for ResolvedCall {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            ResolvedCall::Func(f) => f.hash(state),
            ResolvedCall::Primitive(p) => p.hash(state),
            ResolvedCall::Values(values) => {
                values.len().hash(state);
                for sort in values {
                    // `Arc::ptr_eq` compares only the allocation address and
                    // deliberately ignores trait-object metadata. Hash the
                    // same thin data address so Eq and Hash cannot disagree if
                    // equivalent vtables are duplicated or deduplicated.
                    (Arc::as_ptr(sort) as *const ()).hash(state);
                }
            }
        }
    }
}

impl ResolvedCall {
    pub fn name(&self) -> &str {
        match self {
            ResolvedCall::Func(func) => &func.name,
            ResolvedCall::Primitive(prim) => prim.name(),
            ResolvedCall::Values(_) => "values",
        }
    }

    pub fn output(&self) -> &ArcSort {
        match self {
            ResolvedCall::Func(func) => func.output(),
            ResolvedCall::Primitive(prim) => prim.output(),
            // `values` has no single output; its first column is returned only so that callers
            // that incidentally ask for "a" sort do not panic. Tuple-output uses are routed
            // specially before this is consulted.
            ResolvedCall::Values(values) => &values[0],
        }
    }

    /// Gives the types for a term's child with the given resolved call.
    /// For functions this includes the output sort, for constructors it's just the inputs.
    pub(crate) fn view_types(&self) -> Vec<ArcSort> {
        match self {
            ResolvedCall::Func(func) => {
                let mut types = func.input.clone();
                types.extend(func.outputs.iter().cloned());
                types
            }
            ResolvedCall::Primitive(prim) => prim.input().to_vec(),
            ResolvedCall::Values(values) => values.clone(),
        }
    }

    // Different from `from_resolution`, this function only considers function types and not primitives.
    // As a result, it only requires input argument types, so types.len() == func.input.len(),
    // while for `from_resolution`, types.len() == func.input.len() + 1 to account for the output type
    pub fn from_resolution_func_types(
        head: &str,
        types: &[ArcSort],
        typeinfo: &TypeInfo,
    ) -> Option<ResolvedCall> {
        if let Some(ty) = typeinfo.get_func_type(head) {
            // As long as input types match, a result is returned.
            if ty.input.len() == types.len()
                && ty
                    .input
                    .iter()
                    .zip(types)
                    .all(|(expected, actual)| typeinfo.same_sort(expected, actual))
            {
                return Some(ResolvedCall::Func(ty.clone()));
            }
        }
        None
    }

    pub fn from_resolution(
        head: &str,
        types: &[ArcSort],
        typeinfo: &TypeInfo,
        ctx: crate::Context,
    ) -> ResolvedCall {
        if let Some(ty) = typeinfo.get_func_type(head) {
            let expected = ty.input.iter().chain(ty.outputs.iter());
            if ty.input.len() + ty.outputs.len() == types.len()
                && expected
                    .zip(types)
                    .all(|(expected, actual)| typeinfo.same_sort(expected, actual))
            {
                return ResolvedCall::Func(ty.clone());
            }
        }

        let mut primitives = typeinfo
            .get_prims(head)
            .into_iter()
            .flatten()
            .filter(|p| p.context_ids[ctx].is_some() && p.accept(types, typeinfo));
        if let Some(picked) = primitives.next() {
            if primitives.next().is_some() {
                panic!(
                    "Ambiguous primitive resolution for {head:?} in direct call context {ctx:?}"
                );
            }
            let (out, inp) = types.split_last().unwrap();
            return ResolvedCall::Primitive(SpecializedPrimitive::new(
                picked.clone(),
                inp.to_vec(),
                out.clone(),
                typeinfo,
            ));
        }

        panic!("No resolution for {head:?} in context {ctx:?}");
    }
}

impl Display for ResolvedCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolvedCall::Func(func) => write!(f, "{}", func.name),
            ResolvedCall::Primitive(prim) => write!(f, "{}", prim.name()),
            ResolvedCall::Values(_) => write!(f, "values"),
        }
    }
}

/// A trait encapsulating the ability to query a [`TypeInfo`] to determine
/// whether or not a symbol is bound as a function in the current egglog program.
///
/// Currently, we only use this trait to determine whether a symbol is a
/// [`FunctionSubtype::Constructor`].
pub trait IsFunc {
    fn is_constructor(&self, type_info: &TypeInfo) -> bool;
}

impl IsFunc for ResolvedCall {
    fn is_constructor(&self, _type_info: &TypeInfo) -> bool {
        match self {
            ResolvedCall::Func(func) => func.subtype == FunctionSubtype::Constructor,
            ResolvedCall::Primitive(_) => false,
            ResolvedCall::Values(_) => false,
        }
    }
}

impl IsFunc for String {
    fn is_constructor(&self, type_info: &TypeInfo) -> bool {
        type_info.is_constructor(self)
    }
}

/// Operations on a call head needed to lower the `values` tuple sugar. Implemented for both the
/// unresolved (`String`) and resolved ([`ResolvedCall`]) head representations so that the same
/// lowering code runs in both the type-checking and canonicalization passes.
pub trait HeadOps {
    /// Whether this head is the `values` tuple constructor.
    fn is_values(&self) -> bool;
    /// Whether this head is a tuple-output function (more than one output column).
    fn is_tuple_output(&self, type_info: &TypeInfo) -> bool;
}

impl HeadOps for String {
    fn is_values(&self) -> bool {
        self == "values"
    }
    fn is_tuple_output(&self, type_info: &TypeInfo) -> bool {
        type_info
            .get_func_type(self)
            .is_some_and(|t| t.is_tuple_output())
    }
}

impl HeadOps for ResolvedCall {
    fn is_values(&self) -> bool {
        matches!(self, ResolvedCall::Values(_))
    }
    fn is_tuple_output(&self, _type_info: &TypeInfo) -> bool {
        matches!(self, ResolvedCall::Func(f) if f.is_tuple_output())
    }
}
pub type ResolvedAtomTerm = GenericAtomTerm<ResolvedVar>;

fn atom_term_sort(term: &ResolvedAtomTerm) -> ArcSort {
    match term {
        GenericAtomTerm::Var(_, variable) | GenericAtomTerm::Global(_, variable) => {
            variable.sort.clone()
        }
        GenericAtomTerm::Literal(_, literal) => literal_sort(literal),
    }
}

pub(crate) trait QueryConstraints {
    fn get_constraints(
        &self,
        type_info: &TypeInfo,
        ctx: crate::Context,
    ) -> Result<Vec<Box<dyn Constraint<AtomTerm, ArcSort>>>, TypeError>;

    fn atom_terms(&self) -> HashSet<AtomTerm>;
}

impl QueryConstraints for Query<StringOrEq, String> {
    fn get_constraints(
        &self,
        type_info: &TypeInfo,
        ctx: crate::Context,
    ) -> Result<Vec<Box<dyn Constraint<AtomTerm, ArcSort>>>, TypeError> {
        let mut constraints = vec![];
        for atom in self.atoms.iter() {
            constraints.extend(atom.get_constraints(type_info, ctx)?.into_iter());
        }
        Ok(constraints)
    }

    fn atom_terms(&self) -> HashSet<AtomTerm> {
        self.atoms
            .iter()
            .flat_map(|atom| atom.args.iter().cloned())
            .collect()
    }
}

pub(crate) type ResolvedCoreActions = GenericCoreActions<ResolvedCall, ResolvedVar>;
/// Shared state that threads through lowering from surface actions to core actions.
///
pub(crate) struct CoreActionContext<'a, Head, Leaf, FG> {
    /// Type environment describing functions, constructors, and primitives.
    pub typeinfo: &'a TypeInfo,
    /// Set of variables that are currently in scope during lowering.
    pub binding: &'a mut IndexSet<Leaf>,
    /// Generator used to create fresh symbols for intermediate values.
    pub fresh_gen: &'a mut FG,
    /// Whether we may rewrite `union` on constructors into `set`.
    pub union_to_set_optimization: bool,
    _marker: PhantomData<fn() -> Head>,
}

impl<'a, Head, Leaf, FG> CoreActionContext<'a, Head, Leaf, FG> {
    pub fn new(
        typeinfo: &'a TypeInfo,
        binding: &'a mut IndexSet<Leaf>,
        fresh_gen: &'a mut FG,
        union_to_set_optimization: bool,
    ) -> Self {
        Self {
            typeinfo,
            binding,
            fresh_gen,
            union_to_set_optimization,
            _marker: PhantomData,
        }
    }
}

pub(crate) trait GenericActionsExt<Head, Leaf> {
    #[allow(clippy::type_complexity)]
    fn to_core_actions<FG>(
        &self,
        ctx: &mut CoreActionContext<'_, Head, Leaf, FG>,
    ) -> Result<(GenericCoreActions<Head, Leaf>, MappedActions<Head, Leaf>), TypeError>
    where
        Head: Clone + Display + IsFunc + HeadOps,
        Leaf: AtomLeafAuthority,
        FG: FreshGen<Head, Leaf>;
}

impl<Head, Leaf> GenericActionsExt<Head, Leaf> for GenericActions<Head, Leaf>
where
    Head: Clone + Display + IsFunc + HeadOps,
    Leaf: AtomLeafAuthority,
{
    #[allow(clippy::type_complexity)]
    fn to_core_actions<FG>(
        &self,
        ctx: &mut CoreActionContext<'_, Head, Leaf, FG>,
    ) -> Result<(GenericCoreActions<Head, Leaf>, MappedActions<Head, Leaf>), TypeError>
    where
        Head: Clone + Display + IsFunc + HeadOps,
        Leaf: AtomLeafAuthority,
        FG: FreshGen<Head, Leaf>,
    {
        let mut norm_actions = vec![];
        let mut mapped_actions: MappedActions<Head, Leaf> = GenericActions(vec![]);
        let typeinfo = ctx.typeinfo;
        let union_to_set_optimization = ctx.union_to_set_optimization;

        // During the lowering, there are two important guaratees:
        //   Every used variable should be bound.
        //   Every introduced variable should be unbound before.
        for action in self.0.iter() {
            match action {
                GenericAction::Let(span, var, expr) => {
                    if ctx.binding.contains(var) {
                        return Err(TypeError::AlreadyDefined(var.to_string(), span.clone()));
                    }
                    let mapped_expr = expr.to_core_actions(ctx, &mut norm_actions)?;
                    norm_actions.push(GenericCoreAction::LetAtomTerm(
                        span.clone(),
                        var.clone(),
                        mapped_expr.get_corresponding_var_or_lit_in_scope(typeinfo, ctx.binding),
                    ));
                    mapped_actions.0.push(GenericAction::Let(
                        span.clone(),
                        var.clone(),
                        mapped_expr,
                    ));
                    ctx.binding.insert(var.clone());
                }
                GenericAction::Set(span, head, args, expr) => {
                    let mut mapped_args = vec![];
                    for arg in args {
                        let mapped_arg = arg.to_core_actions(ctx, &mut norm_actions)?;
                        mapped_args.push(mapped_arg);
                    }
                    // The value may be a `(values v...)` tuple (for a tuple-output function), which
                    // contributes one output column per element; otherwise it is a single value.
                    let (mapped_value, value_terms) = match expr {
                        GenericExpr::Call(vspan, vhead, vargs) if vhead.is_values() => {
                            let mut mapped = vec![];
                            let mut terms = vec![];
                            for v in vargs {
                                let m = v.to_core_actions(ctx, &mut norm_actions)?;
                                terms.push(
                                    m.get_corresponding_var_or_lit_in_scope(typeinfo, ctx.binding),
                                );
                                mapped.push(m);
                            }
                            let dummy = ctx.fresh_gen.fresh(vhead);
                            let mapped_call = GenericExpr::Call(
                                vspan.clone(),
                                CorrespondingVar::new(vhead.clone(), dummy),
                                mapped,
                            );
                            (mapped_call, terms)
                        }
                        _ => {
                            let m = expr.to_core_actions(ctx, &mut norm_actions)?;
                            let term =
                                m.get_corresponding_var_or_lit_in_scope(typeinfo, ctx.binding);
                            (m, vec![term])
                        }
                    };
                    norm_actions.push(GenericCoreAction::Set(
                        span.clone(),
                        head.clone(),
                        mapped_args
                            .iter()
                            .map(|e| e.get_corresponding_var_or_lit_in_scope(typeinfo, ctx.binding))
                            .collect(),
                        value_terms,
                    ));
                    let v = ctx.fresh_gen.fresh(head);
                    mapped_actions.0.push(GenericAction::Set(
                        span.clone(),
                        CorrespondingVar::new(head.clone(), v),
                        mapped_args,
                        mapped_value,
                    ));
                }
                GenericAction::Change(span, change, head, args) => {
                    let mut mapped_args = vec![];
                    for arg in args {
                        let mapped_arg = arg.to_core_actions(ctx, &mut norm_actions)?;
                        mapped_args.push(mapped_arg);
                    }
                    norm_actions.push(GenericCoreAction::Change(
                        span.clone(),
                        *change,
                        head.clone(),
                        mapped_args
                            .iter()
                            .map(|e| e.get_corresponding_var_or_lit_in_scope(typeinfo, ctx.binding))
                            .collect(),
                    ));
                    let v = ctx.fresh_gen.fresh(head);
                    mapped_actions.0.push(GenericAction::Change(
                        span.clone(),
                        *change,
                        CorrespondingVar::new(head.clone(), v),
                        mapped_args,
                    ));
                }
                GenericAction::Union(span, e1, e2) => {
                    // Optimization: if one side is a constructor call and the other side is a variable,
                    // we can lower this to a Set action instead of a Union action.
                    // This produces invalid egglog, since top-level egglog expects only Union on constructors.
                    // We disable this with union_to_set_optimization flag for term/proof mode.
                    // TODO move this optimization to later stage so we can keep it enabled in term/proof mode.
                    match (e1, e2) {
                        (var @ GenericExpr::Var(..), GenericExpr::Call(_, f, args))
                        | (GenericExpr::Call(_, f, args), var @ GenericExpr::Var(..))
                            if f.is_constructor(typeinfo) && union_to_set_optimization =>
                        {
                            let head = f;
                            let expr = var;
                            let mut mapped_args = vec![];
                            for arg in args {
                                let mapped_arg = arg.to_core_actions(ctx, &mut norm_actions)?;
                                mapped_args.push(mapped_arg);
                            }
                            let mapped_expr = expr.to_core_actions(ctx, &mut norm_actions)?;
                            norm_actions.push(GenericCoreAction::Set(
                                span.clone(),
                                head.clone(),
                                mapped_args
                                    .iter()
                                    .map(|e| {
                                        e.get_corresponding_var_or_lit_in_scope(
                                            typeinfo,
                                            ctx.binding,
                                        )
                                    })
                                    .collect(),
                                // Constructors are single-output, so a single value column.
                                vec![
                                    mapped_expr.get_corresponding_var_or_lit_in_scope(
                                        typeinfo,
                                        ctx.binding,
                                    ),
                                ],
                            ));
                            let v = ctx.fresh_gen.fresh(head);
                            mapped_actions.0.push(GenericAction::Set(
                                span.clone(),
                                CorrespondingVar::new(head.clone(), v),
                                mapped_args,
                                mapped_expr,
                            ));
                        }
                        _ => {
                            let mapped_e1 = e1.to_core_actions(ctx, &mut norm_actions)?;
                            let mapped_e2 = e2.to_core_actions(ctx, &mut norm_actions)?;
                            norm_actions.push(GenericCoreAction::Union(
                                span.clone(),
                                mapped_e1
                                    .get_corresponding_var_or_lit_in_scope(typeinfo, ctx.binding),
                                mapped_e2
                                    .get_corresponding_var_or_lit_in_scope(typeinfo, ctx.binding),
                            ));
                            mapped_actions.0.push(GenericAction::Union(
                                span.clone(),
                                mapped_e1,
                                mapped_e2,
                            ));
                        }
                    };
                }
                GenericAction::Panic(span, string) => {
                    norm_actions.push(GenericCoreAction::Panic(span.clone(), string.clone()));
                    mapped_actions
                        .0
                        .push(GenericAction::Panic(span.clone(), string.clone()));
                }
                GenericAction::Expr(span, expr) => {
                    let mapped_expr = expr.to_core_actions(ctx, &mut norm_actions)?;
                    mapped_actions
                        .0
                        .push(GenericAction::Expr(span.clone(), mapped_expr));
                }
            }
        }
        Ok((GenericCoreActions::new(norm_actions), mapped_actions))
    }
}

pub(crate) trait GenericExprExt<Head, Leaf>
where
    Head: Clone + Display,
    Leaf: AtomLeafAuthority,
{
    fn to_query(
        &self,
        typeinfo: &TypeInfo,
        fresh_gen: &mut impl FreshGen<Head, Leaf>,
    ) -> (
        Vec<GenericAtom<HeadOrEq<Head>, Leaf>>,
        MappedExpr<Head, Leaf>,
    );

    fn to_core_actions<FG: FreshGen<Head, Leaf>>(
        &self,
        ctx: &mut CoreActionContext<'_, Head, Leaf, FG>,
        out_actions: &mut Vec<GenericCoreAction<Head, Leaf>>,
    ) -> Result<MappedExpr<Head, Leaf>, TypeError>;
}

impl<Head, Leaf> GenericExprExt<Head, Leaf> for GenericExpr<Head, Leaf>
where
    Head: Clone + Display,
    Leaf: AtomLeafAuthority,
{
    fn to_query(
        &self,
        typeinfo: &TypeInfo,
        fresh_gen: &mut impl FreshGen<Head, Leaf>,
    ) -> (
        Vec<GenericAtom<HeadOrEq<Head>, Leaf>>,
        MappedExpr<Head, Leaf>,
    )
    where
        Head: Clone + Display,
        Leaf: AtomLeafAuthority,
    {
        match self {
            GenericExpr::Lit(span, lit) => (vec![], GenericExpr::Lit(span.clone(), lit.clone())),
            GenericExpr::Var(span, v) => (vec![], GenericExpr::Var(span.clone(), v.clone())),
            GenericExpr::Call(span, f, children) => {
                let fresh = fresh_gen.fresh(f);
                let mut new_children = vec![];
                let mut atoms = vec![];
                let mut child_exprs = vec![];
                for child in children {
                    let (child_atoms, child_expr) = child.to_query(typeinfo, fresh_gen);
                    let child_atomterm = child_expr.get_corresponding_var_or_lit(typeinfo);
                    new_children.push(child_atomterm);
                    atoms.extend(child_atoms);
                    child_exprs.push(child_expr);
                }
                let args = {
                    new_children.push(GenericAtomTerm::Var(span.clone(), fresh.clone()));
                    new_children
                };
                atoms.push(GenericAtom {
                    span: span.clone(),
                    head: HeadOrEq::Head(f.clone()),
                    args,
                });
                (
                    atoms,
                    GenericExpr::Call(
                        span.clone(),
                        CorrespondingVar::new(f.clone(), fresh),
                        child_exprs,
                    ),
                )
            }
        }
    }

    fn to_core_actions<FG: FreshGen<Head, Leaf>>(
        &self,
        ctx: &mut CoreActionContext<'_, Head, Leaf, FG>,
        out_actions: &mut Vec<GenericCoreAction<Head, Leaf>>,
    ) -> Result<MappedExpr<Head, Leaf>, TypeError> {
        let typeinfo = ctx.typeinfo;
        match self {
            GenericExpr::Lit(span, lit) => Ok(GenericExpr::Lit(span.clone(), lit.clone())),
            GenericExpr::Var(span, v) => {
                let sym = v.to_string();
                if ctx.binding.contains(v) || typeinfo.is_global(&sym) {
                    Ok(GenericExpr::Var(span.clone(), v.clone()))
                } else {
                    Err(TypeError::Unbound(sym, span.clone()))
                }
            }
            GenericExpr::Call(span, f, args) => {
                let mut norm_args = vec![];
                let mut mapped_args = vec![];
                for arg in args {
                    let mapped_arg = arg.to_core_actions(ctx, out_actions)?;
                    norm_args.push(
                        mapped_arg.get_corresponding_var_or_lit_in_scope(typeinfo, ctx.binding),
                    );
                    mapped_args.push(mapped_arg);
                }
                let var = ctx.fresh_gen.fresh(f);
                ctx.binding.insert(var.clone());
                out_actions.push(GenericCoreAction::Let(
                    span.clone(),
                    var.clone(),
                    f.clone(),
                    norm_args,
                ));
                Ok(GenericExpr::Call(
                    span.clone(),
                    CorrespondingVar::new(f.clone(), var),
                    mapped_args,
                ))
            }
        }
    }
}

pub(crate) type CoreRule = GenericCoreRule<StringOrEq, String, String>;
pub(crate) type ResolvedCoreRule = GenericCoreRule<ResolvedCall, ResolvedCall, ResolvedVar>;

trait CoreRuleSubst<Leaf> {
    fn subst(&mut self, subst: &HashMap<Leaf, GenericAtomTerm<Leaf>>);
}

impl<BodyCall, ActionCall, Leaf> CoreRuleSubst<Leaf> for GenericCoreRule<BodyCall, ActionCall, Leaf>
where
    Leaf: Clone + Eq + Hash,
{
    fn subst(&mut self, subst: &HashMap<Leaf, GenericAtomTerm<Leaf>>) {
        for atom in &mut self.body.atoms {
            atom.substitute_with(&mut |variable| subst.get(variable).cloned());
        }
        let substitutions = subst.iter().map(|(variable, term)| {
            GenericCoreAction::LetAtomTerm(term.span().clone(), variable.clone(), term.clone())
        });
        let actions = std::mem::take(&mut self.head.0);
        self.head.0 = substitutions.chain(actions).collect();
    }
}

trait CanonicalizeCoreRule<Head, Leaf> {
    fn canonicalize(
        self,
        value_eq: impl Fn(&GenericAtomTerm<Leaf>, &GenericAtomTerm<Leaf>) -> Head,
    ) -> GenericCoreRule<Head, Head, Leaf>;
}

impl<Head, Leaf> CanonicalizeCoreRule<Head, Leaf> for GenericCoreRule<HeadOrEq<Head>, Head, Leaf>
where
    Leaf: Eq + Clone + Hash + Debug,
    Head: Clone,
{
    /// Transformed a UnresolvedCoreRule into a CanonicalizedCoreRule.
    /// In particular, it removes equality checks between variables and
    /// other arguments, and turns equality checks between non-variable arguments
    /// into a primitive equality check `value-eq`.
    fn canonicalize(
        self,
        // Users need to pass in a substitute for equality constraints.
        value_eq: impl Fn(&GenericAtomTerm<Leaf>, &GenericAtomTerm<Leaf>) -> Head,
    ) -> GenericCoreRule<Head, Head, Leaf> {
        let mut result_rule = self;
        loop {
            let mut to_subst = None;
            for atom in result_rule.body.atoms.iter() {
                if atom.head.is_eq() && atom.args[0] != atom.args[1] {
                    match &atom.args[..] {
                        [GenericAtomTerm::Var(_, x), y] | [y, GenericAtomTerm::Var(_, x)] => {
                            to_subst = Some((x, y));
                            break;
                        }
                        _ => (),
                    }
                }
            }
            if let Some((x, y)) = to_subst {
                let subst = HashMap::from_iter([(x.clone(), y.clone())]);
                result_rule.subst(&subst);
            } else {
                break;
            }
        }

        let atoms = result_rule
            .body
            .atoms
            .into_iter()
            .filter_map(|atom| match atom.head {
                HeadOrEq::Eq => {
                    assert_eq!(atom.args.len(), 2);
                    match (&atom.args[0], &atom.args[1]) {
                        (GenericAtomTerm::Var(_, v1), GenericAtomTerm::Var(_, v2)) => {
                            assert_eq!(v1, v2);
                            None
                        }
                        (GenericAtomTerm::Var(..), _) | (_, GenericAtomTerm::Var(..)) => {
                            panic!("equalities between variable and non-variable arguments should have been canonicalized")
                        }
                        (at1, at2) => {
                            if at1 == at2 {
                                None
                            } else {
                                Some(GenericAtom {
                                    span: atom.span.clone(),
                                    head: value_eq(&atom.args[0], &atom.args[1]),
                                    args: vec![
                                        atom.args[0].clone(),
                                        atom.args[1].clone(),
                                        GenericAtomTerm::Literal(atom.span.clone(), Literal::Unit),
                                    ],
                                })
                            }
                        },
                    }
                }
                HeadOrEq::Head(symbol) => Some(GenericAtom {
                    span: atom.span.clone(),
                    head: symbol,
                    args: atom.args,
                }),
            })
            .collect();
        GenericCoreRule {
            span: result_rule.span,
            body: Query { atoms },
            head: result_rule.head,
        }
    }
}

fn equiv_groups_to_eq_constraints<Head, Leaf>(
    groups: &HashMap<(Head, Vec<GenericAtomTerm<Leaf>>), Vec<GenericAtomTerm<Leaf>>>,
    span: &Span,
) -> Vec<GenericAtom<HeadOrEq<Head>, Leaf>>
where
    Leaf: Eq + Clone + Hash + Debug,
    Head: Clone,
{
    let mut eq_constraints = vec![];
    for group in groups.values() {
        let first = &group[0];
        for other in &group[1..] {
            if first == other {
                continue;
            }
            eq_constraints.push(GenericAtom {
                span: span.clone(),
                head: HeadOrEq::Eq,
                args: vec![first.clone(), other.clone()],
            });
        }
    }
    eq_constraints
}

trait RemoveDuplicateVars<Head, Leaf> {
    fn remove_dup_vars(
        self,
        value_eq: impl Fn(&GenericAtomTerm<Leaf>, &GenericAtomTerm<Leaf>) -> Head,
    ) -> Self;
}

impl<Head, Leaf> RemoveDuplicateVars<Head, Leaf> for GenericCoreRule<Head, Head, Leaf>
where
    Leaf: Eq + Clone + Hash + Debug,
    Head: Clone + Eq + Hash,
{
    /// Functions in egglog follow functional dependency, and this pass removes
    /// duplicate variables based on functional dependencies.
    /// For example, if we have two atoms `R(x, y, z1)` and `R(x, y, z2)`,
    /// then we can remove one of them and add an equality constraint `z1 = z2`.
    /// This is done until fixpoint, so it is kind of like rebuilding.
    fn remove_dup_vars(
        mut self,
        value_eq: impl Fn(&GenericAtomTerm<Leaf>, &GenericAtomTerm<Leaf>) -> Head,
    ) -> Self {
        // Maps function calls to sets of equivalent variables to be deduplicated
        let mut groups: HashMap<(Head, Vec<GenericAtomTerm<Leaf>>), Vec<GenericAtomTerm<Leaf>>> =
            HashMap::default();

        // Remove entries wit identical (head, inputs) pair and mark respective outputs to be merged.
        self.body.atoms.retain(|atom| {
            let (out, inp) = atom.args.split_last().unwrap();
            let key = (atom.head.clone(), inp.to_owned());
            let group = groups.entry(key).or_default();
            group.push(out.clone());
            group.len() == 1
        });

        let new_atoms = equiv_groups_to_eq_constraints(&groups, &self.span);

        if new_atoms.is_empty() {
            self
        } else {
            let atoms: Vec<GenericAtom<HeadOrEq<Head>, Leaf>> = new_atoms
                .into_iter()
                .chain(self.body.atoms.into_iter().map(|atom| GenericAtom {
                    span: atom.span,
                    head: HeadOrEq::Head(atom.head),
                    args: atom.args,
                }))
                .collect();

            GenericCoreRule {
                span: self.span,
                body: Query { atoms },
                head: self.head,
            }
            .canonicalize(&value_eq)
            .remove_dup_vars(value_eq)
        }
    }
}

pub(crate) trait GenericRuleExt<Head, Leaf> {
    fn to_core_rule(
        &self,
        typeinfo: &TypeInfo,
        fresh_gen: &mut impl FreshGen<Head, Leaf>,
        union_to_set_optimization: bool,
    ) -> Result<GenericCoreRule<HeadOrEq<Head>, Head, Leaf>, TypeError>
    where
        Head: Clone + Display + IsFunc + HeadOps,
        Leaf: AtomLeafAuthority + Debug;
}

impl<Head, Leaf> GenericRuleExt<Head, Leaf> for GenericRule<Head, Leaf>
where
    Head: Clone + Display + IsFunc + HeadOps,
    Leaf: AtomLeafAuthority + Debug,
{
    fn to_core_rule(
        &self,
        typeinfo: &TypeInfo,
        fresh_gen: &mut impl FreshGen<Head, Leaf>,
        union_to_set_optimization: bool,
    ) -> Result<GenericCoreRule<HeadOrEq<Head>, Head, Leaf>, TypeError>
    where
        Head: Clone + Display + IsFunc + HeadOps,
        Leaf: AtomLeafAuthority + Debug,
    {
        let (body, _correspondence) = Facts(self.body.clone()).to_query(typeinfo, fresh_gen);
        let mut binding = body.vars().collect::<IndexSet<_>>();
        let mut ctx =
            CoreActionContext::new(typeinfo, &mut binding, fresh_gen, union_to_set_optimization);
        let (head, _correspondence) = self.head.to_core_actions(&mut ctx)?;
        Ok(GenericCoreRule {
            span: self.span.clone(),
            body,
            head,
        })
    }
}

pub(crate) trait ResolvedRuleExt {
    fn to_canonicalized_core_rule(
        &self,
        typeinfo: &TypeInfo,
        fresh_gen: &mut SymbolGen,
        union_to_set_optimization: bool,
    ) -> Result<ResolvedCoreRule, TypeError>;
}

impl ResolvedRuleExt for ResolvedRule {
    fn to_canonicalized_core_rule(
        &self,
        typeinfo: &TypeInfo,
        fresh_gen: &mut SymbolGen,
        union_to_set_optimization: bool,
    ) -> Result<ResolvedCoreRule, TypeError> {
        let value_eq = typeinfo.value_eq_primitive().unwrap_or_else(|| {
            panic!("frontend did not register exact value-eq primitive authority")
        });
        let value_eq = |at1: &ResolvedAtomTerm, at2: &ResolvedAtomTerm| {
            ResolvedCall::Primitive(SpecializedPrimitive::new(
                value_eq.clone(),
                vec![atom_term_sort(at1), atom_term_sort(at2)],
                UnitSort.to_arcsort(),
                typeinfo,
            ))
        };

        let rule = self.to_core_rule(typeinfo, fresh_gen, union_to_set_optimization)?;

        // The groundedness check happens before canonicalization, because canonicalization
        // may turn ungrounded variables in a query to unbounded variables in actions (e.g.,
        // `(rule ((= x y)) ((R x y)))`) but unboundedness is only checked during type checking.
        grounded_check(&rule)?;

        let rule = rule.canonicalize(&value_eq);

        let rule = rule.remove_dup_vars(value_eq);

        Ok(rule)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    #[derive(Clone)]
    struct ScopedIdentityPrimitive(&'static str);

    impl Primitive for ScopedIdentityPrimitive {
        fn name(&self) -> &str {
            self.0
        }

        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            crate::constraint::SimpleTypeConstraint::new(
                self.0,
                vec![I64Sort.to_arcsort(), I64Sort.to_arcsort()],
                span.clone(),
            )
            .into_box()
        }
    }

    impl PurePrim for ScopedIdentityPrimitive {
        fn apply<'a, 'db>(&self, _state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
            args.first().copied()
        }
    }

    type TestCoreRule = GenericCoreRule<String, String, String>;

    fn make_var(name: &str) -> GenericAtomTerm<String> {
        GenericAtomTerm::Var(span!(), name.to_string())
    }

    fn make_atom(head: &str, args: Vec<&str>) -> GenericAtom<String, String> {
        GenericAtom {
            span: span!(),
            head: head.to_string(),
            args: args.into_iter().map(make_var).collect(),
        }
    }

    fn value_eq_string(_at1: &GenericAtomTerm<String>, _at2: &GenericAtomTerm<String>) -> String {
        "value-eq".to_string()
    }

    fn hash_value(value: &impl Hash) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn specialized_primitive_identity_uses_registration_not_runtime_tokens() {
        let egraph = EGraph::default();
        let min = egraph.type_info.get_prims("ordering-min").unwrap()[0].clone();
        let max = egraph.type_info.get_prims("ordering-max").unwrap()[0].clone();
        assert_ne!(min.registration_id(), max.registration_id());
        assert_ne!(min.context_ids, max.context_ids);

        let sort = egraph.get_sort_by_name("i64").unwrap().clone();
        let specialize = |registration: PrimitiveWithId| {
            SpecializedPrimitive::new(
                registration,
                vec![sort.clone(), sort.clone()],
                sort.clone(),
                &egraph.type_info,
            )
        };

        let original = specialize(min.clone());
        let mut same_registration_new_runtime_tokens = min;
        same_registration_new_runtime_tokens.context_ids = max.context_ids;
        let retokened = specialize(same_registration_new_runtime_tokens);
        assert_eq!(original, retokened);
        assert_eq!(hash_value(&original), hash_value(&retokened));

        let different_registration = specialize(max);
        assert_ne!(original, different_registration);
    }

    #[test]
    fn primitive_registration_authority_is_not_reused_after_pop() {
        let mut egraph = EGraph::default();
        let i64_sort = egraph.get_sort_by_name("i64").unwrap().clone();

        egraph.push();
        egraph.add_pure_primitive(ScopedIdentityPrimitive("popped-identity"), None);
        let popped_registration = egraph.type_info.get_prims("popped-identity").unwrap()[0].clone();
        let popped = SpecializedPrimitive::new(
            popped_registration,
            vec![i64_sort.clone()],
            i64_sort.clone(),
            &egraph.type_info,
        );

        egraph.pop().unwrap();
        egraph.add_pure_primitive(ScopedIdentityPrimitive("replacement-identity"), None);
        let replacement_registration =
            egraph.type_info.get_prims("replacement-identity").unwrap()[0].clone();
        assert_ne!(
            popped.registration_id(),
            replacement_registration.registration_id(),
            "pop reused a primitive authority retained by resolved IR"
        );
        let replacement = SpecializedPrimitive::new(
            replacement_registration,
            vec![i64_sort.clone()],
            i64_sort,
            &egraph.type_info,
        );
        assert_ne!(popped, replacement);
        assert_ne!(hash_value(&popped), hash_value(&replacement));
    }

    #[test]
    fn primitive_specialization_and_values_use_exact_sort_registrations() {
        let mut egraph = EGraph::default();
        egraph.declare_sort("Left", &None, span!()).unwrap();
        egraph.declare_sort("Right", &None, span!()).unwrap();
        let left = egraph.get_sort_by_name("Left").unwrap().clone();
        let right = egraph.get_sort_by_name("Right").unwrap().clone();
        let registration = egraph.type_info.get_prims("ordering-min").unwrap()[0].clone();

        let left_specialization = SpecializedPrimitive::new(
            registration.clone(),
            vec![left.clone(), left.clone()],
            left.clone(),
            &egraph.type_info,
        );
        let right_specialization = SpecializedPrimitive::new(
            registration,
            vec![right.clone(), right.clone()],
            right.clone(),
            &egraph.type_info,
        );
        assert_ne!(left_specialization, right_specialization);
        assert_ne!(
            hash_value(&left_specialization),
            hash_value(&right_specialization)
        );
        assert_ne!(
            left_specialization.output_identity(),
            right_specialization.output_identity()
        );
        assert_ne!(
            left_specialization.input_identities(),
            right_specialization.input_identities()
        );

        let left_values = ResolvedCall::Values(vec![left.clone()]);
        let left_values_clone = ResolvedCall::Values(vec![left]);
        let right_values = ResolvedCall::Values(vec![right]);
        assert_eq!(left_values, left_values_clone);
        assert_eq!(hash_value(&left_values), hash_value(&left_values_clone));
        assert_ne!(left_values, right_values);
        assert_ne!(hash_value(&left_values), hash_value(&right_values));
    }

    #[test]
    fn view_qualified_primitive_collisions_do_not_alias_specializations() {
        let mut proof_mode = EGraph::new_compile_only(true);
        proof_mode
            .resolve_program_compile_only(None, "(sort ViewLocal)")
            .unwrap();
        let proof_check = proof_mode
            .proof_state
            .original_typechecking
            .as_deref()
            .expect("proof mode retains a proof-check catalog");

        let execution_sort = proof_mode.get_sort_by_name("ViewLocal").unwrap().clone();
        let proof_sort = proof_check.get_sort_by_name("ViewLocal").unwrap().clone();
        let execution_values = ResolvedCall::Values(vec![execution_sort.clone()]);
        let execution_values_clone = ResolvedCall::Values(vec![execution_sort.clone()]);
        assert_eq!(execution_values, execution_values_clone);
        let same_named_decoy: ArcSort = Arc::new(EqSort {
            name: "ViewLocal".to_owned(),
        });
        assert!(
            proof_mode
                .type_info
                .canonical_sort_arc(&same_named_decoy)
                .is_none()
        );
        assert_ne!(
            execution_values,
            ResolvedCall::Values(vec![same_named_decoy])
        );

        let execution_primitive =
            proof_mode.type_info.get_prims("ordering-min").unwrap()[0].clone();
        let proof_primitive = proof_check.type_info.get_prims("ordering-min").unwrap()[0].clone();
        assert_eq!(
            execution_primitive.registration_id(),
            proof_primitive.registration_id(),
            "the canary requires a colliding primitive ordinal"
        );
        let execution_specialization = SpecializedPrimitive::new(
            execution_primitive,
            vec![execution_sort.clone(), execution_sort.clone()],
            execution_sort,
            &proof_mode.type_info,
        );
        let proof_specialization = SpecializedPrimitive::new(
            proof_primitive,
            vec![proof_sort.clone(), proof_sort.clone()],
            proof_sort,
            &proof_check.type_info,
        );
        assert_ne!(execution_specialization, proof_specialization);
        assert_ne!(
            hash_value(&execution_specialization),
            hash_value(&proof_specialization)
        );
    }

    #[test]
    fn test_remove_dup_vars_basic() {
        let rule = TestCoreRule {
            span: span!(),
            body: Query {
                atoms: vec![
                    make_atom("R", vec!["x", "y", "z1"]),
                    make_atom("R", vec!["x", "y", "z2"]),
                    make_atom("R", vec!["x", "z3"]),
                    make_atom("R", vec!["a", "b", "z4"]),
                    make_atom("R", vec!["c", "d", "z5"]),
                ],
            },
            head: GenericCoreActions::default(),
        };

        let result = rule.remove_dup_vars(value_eq_string);

        assert_eq!(result.body.atoms.len(), 4);
        assert_eq!(result.body.atoms[0].head, "R");
        assert_eq!(result.body.atoms[0].args[0], make_var("x"));
        assert_eq!(result.body.atoms[0].args[1], make_var("y"));
        assert_eq!(result.body.atoms[1].args.len(), 2);
    }

    #[test]
    fn test_remove_dup_vars_fixpoint() {
        // Test: R(x, y, z1), R(x, y, z2), R(x, y, z3) should all get unified
        // This tests that the fixpoint iteration works correctly
        let rule = TestCoreRule {
            span: span!(),
            body: Query {
                atoms: vec![
                    make_atom("R", vec!["x", "y", "z1"]),
                    make_atom("R", vec!["x", "y", "z2"]),
                    make_atom("R", vec!["x", "y", "z3"]),
                    make_atom("S", vec!["z1", "z2", "z3"]),
                    make_atom("S", vec!["z2", "z1", "z4"]),
                ],
            },
            head: GenericCoreActions::default(),
        };

        let result = rule.remove_dup_vars(value_eq_string);

        assert_eq!(result.body.atoms.len(), 2);
        assert_eq!(result.body.atoms[0].head, "R");
        assert_eq!(result.body.atoms[0].args[0], make_var("x"));
        assert_eq!(result.body.atoms[0].args[1], make_var("y"));
        assert_eq!(result.body.atoms[1].args[0], result.body.atoms[1].args[1]);

        let rule = TestCoreRule {
            span: span!(),
            body: Query {
                atoms: vec![
                    make_atom("R", vec!["x", "y", "z1"]),
                    make_atom("R", vec!["x", "y", "z2"]),
                    make_atom("R", vec!["x", "y", "z3"]),
                    make_atom("R", vec!["z1", "z2", "z1"]),
                    make_atom("R", vec!["z2", "z1", "x"]),
                    make_atom("R", vec!["z2", "z2", "y"]),
                ],
            },
            head: GenericCoreActions::default(),
        };

        let result = rule.remove_dup_vars(value_eq_string);

        assert_eq!(result.body.atoms.len(), 1);
        assert_eq!(result.body.atoms[0].head, "R");
        assert_eq!(result.body.atoms[0].args[0], result.body.atoms[0].args[1]);
        assert_eq!(result.body.atoms[0].args[0], result.body.atoms[0].args[2]);
    }

    #[test]
    fn test_remove_dup_vars_with_actions_using_removed_var() {
        let rule = TestCoreRule {
            span: span!(),
            body: Query {
                atoms: vec![
                    make_atom("R", vec!["x", "y", "z1"]),
                    make_atom("R", vec!["x", "y", "z2"]),
                ],
            },
            head: GenericCoreActions(vec![GenericCoreAction::Union(
                span!(),
                make_var("z2"),
                make_var("z1"),
            )]),
        };

        let result = rule.remove_dup_vars(value_eq_string);

        assert_eq!(result.body.atoms.len(), 1);
        assert!(matches!(
            &result.head.0.as_slice(),
            &[
                GenericCoreAction::LetAtomTerm(_, _, _),
                GenericCoreAction::Union(_, _, _)
            ]
        ));
    }
}

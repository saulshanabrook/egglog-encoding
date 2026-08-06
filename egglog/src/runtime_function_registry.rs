//! Exact runtime registry for frontend-resolved function tables.
//!
//! Source commands and public inspection APIs still begin with a spelling, so
//! the registry retains a name index for that unresolved boundary.  Once a
//! [`FuncType`](crate::typechecking::FuncType) exists, its
//! [`FunctionRegistrationId`](crate::typechecking::FunctionRegistrationId) is
//! the sole semantic lookup key.  A missing exact identity is an invariant
//! error; callers must never retry by diagnostic name or schema.

use std::fmt::{self, Display, Formatter};

use crate::Function;
use crate::ast::ResolvedFunctionDecl;
use crate::typechecking::{
    CallableIdentity, FuncType, FunctionRegistrationId, IndexRegistrationId,
};
use crate::util::{HashMap, IndexMap};
use crate::{Error, ResolvedCall, ResolvedSchema};

impl Function {
    /// Construct runtime metadata from the exact resolved declaration.
    ///
    /// Untyped schema strings are deliberately ignored. The `FuncType` selected
    /// by frontend resolution owns the runtime schema and callable identity.
    pub(crate) fn from_resolved_decl(
        decl: ResolvedFunctionDecl,
        can_subsume: bool,
        backend_id: egglog_bridge::FunctionId,
    ) -> Result<Self, Error> {
        let ResolvedCall::Func(function_type) = &decl.resolved_schema else {
            return Err(Error::BackendError(format!(
                "resolved declaration {:?} does not carry function authority",
                decl.name
            )));
        };
        if !matches!(function_type.identity, CallableIdentity::Function(_)) {
            return Err(Error::BackendError(format!(
                "resolved declaration {:?} carries read-only index authority",
                decl.name
            )));
        }
        if decl.subtype != function_type.subtype {
            return Err(Error::BackendError(format!(
                "resolved declaration {:?} has inconsistent subtype metadata",
                decl.name
            )));
        }
        let schema = ResolvedSchema {
            input: function_type.input.clone(),
            outputs: function_type.outputs.clone(),
        };
        Ok(Self {
            decl,
            schema,
            can_subsume,
            backend_id,
        })
    }

    pub(crate) fn resolved_type(&self) -> &FuncType {
        let ResolvedCall::Func(function_type) = &self.decl.resolved_schema else {
            unreachable!("runtime function was constructed without exact function authority")
        };
        function_type
    }

    pub(crate) fn registration_id(&self) -> FunctionRegistrationId {
        let CallableIdentity::Function(identity) = self.resolved_type().identity else {
            unreachable!("runtime function was constructed with exact index authority")
        };
        identity
    }
}

/// An error that leaves the registry unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RuntimeFunctionRegistryError {
    DuplicateIdentity(FunctionRegistrationId),
    DuplicateName(String),
}

impl Display for RuntimeFunctionRegistryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateIdentity(identity) => write!(
                f,
                "runtime function registration {} was published more than once",
                identity.ordinal()
            ),
            Self::DuplicateName(name) => {
                write!(
                    f,
                    "runtime function name {name:?} was published more than once"
                )
            }
        }
    }
}

impl From<RuntimeFunctionRegistryError> for Error {
    fn from(error: RuntimeFunctionRegistryError) -> Self {
        Self::BackendError(error.to_string())
    }
}

/// A resolved callable that cannot name one of this registry's function tables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExactFunctionLookupError {
    Index(IndexRegistrationId),
    Missing(FunctionRegistrationId),
}

impl Display for ExactFunctionLookupError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Index(identity) => write!(
                f,
                "resolved callable is read-only index registration {}",
                identity.ordinal()
            ),
            Self::Missing(identity) => write!(
                f,
                "resolved function registration {} is absent from the runtime registry",
                identity.ordinal()
            ),
        }
    }
}

impl From<ExactFunctionLookupError> for Error {
    fn from(error: ExactFunctionLookupError) -> Self {
        Self::BackendError(error.to_string())
    }
}

/// One authoritative runtime table registry.
///
/// `by_name` is only a source/public-API index. `declaration_order` is retained
/// independently so display order cannot accidentally become lookup authority.
#[derive(Clone, Default)]
pub(crate) struct RuntimeFunctionRegistry {
    by_id: HashMap<FunctionRegistrationId, Function>,
    by_name: IndexMap<String, FunctionRegistrationId>,
    declaration_order: Vec<FunctionRegistrationId>,
}

impl RuntimeFunctionRegistry {
    pub(crate) fn contains_name(&self, name: &str) -> bool {
        self.by_name.contains_key(name)
    }

    /// Resolve source/public syntax by its prefix-visible spelling.
    pub(crate) fn get_by_name(&self, name: &str) -> Option<&Function> {
        let identity = *self.by_name.get(name)?;
        self.by_id.get(&identity)
    }

    pub(crate) fn require_by_id(
        &self,
        identity: FunctionRegistrationId,
    ) -> Result<&Function, ExactFunctionLookupError> {
        self.by_id
            .get(&identity)
            .ok_or(ExactFunctionLookupError::Missing(identity))
    }

    /// Resolve an already-typechecked call using exact nominal authority.
    ///
    /// An index is not a function table and therefore never resolves here,
    /// even if its diagnostic name matches a registered function.
    pub(crate) fn require_exact(
        &self,
        function: &FuncType,
    ) -> Result<&Function, ExactFunctionLookupError> {
        match function.identity {
            CallableIdentity::Function(identity) => self.require_by_id(identity),
            CallableIdentity::Index(identity) => Err(ExactFunctionLookupError::Index(identity)),
        }
    }

    /// Atomically publish one fully constructed function.
    ///
    /// Both indexes are derived from the function's own exact descriptor so a
    /// caller cannot provide a mismatched semantic key or diagnostic spelling.
    pub(crate) fn insert(
        &mut self,
        function: Function,
    ) -> Result<(), RuntimeFunctionRegistryError> {
        let identity = function.registration_id();
        let name = function.name().to_owned();
        if self.by_id.contains_key(&identity) {
            return Err(RuntimeFunctionRegistryError::DuplicateIdentity(identity));
        }
        if self.by_name.contains_key(&name) {
            return Err(RuntimeFunctionRegistryError::DuplicateName(name));
        }

        self.by_id.insert(identity, function);
        self.by_name.insert(name, identity);
        self.declaration_order.push(identity);
        Ok(())
    }

    pub(crate) fn iter_in_declaration_order(
        &self,
    ) -> impl ExactSizeIterator<Item = (&String, &Function)> {
        self.declaration_order.iter().map(|identity| {
            let function = self
                .by_id
                .get(identity)
                .expect("runtime function declaration order references a missing exact identity");
            (&function.decl.name, function)
        })
    }

    pub(crate) fn len(&self) -> usize {
        self.by_id.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.by_id.is_empty()
    }

    #[cfg(test)]
    fn exact_id_for_name(&self, name: &str) -> Option<FunctionRegistrationId> {
        self.by_name.get(name).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn resolved_decl(identity: FunctionRegistrationId, name: &str) -> ResolvedFunctionDecl {
        use crate::ast::{FunctionSubtype, GenericFunctionDecl, Schema, Span};
        use crate::sort::I64Sort;
        use crate::{ResolvedCall, prelude::BaseSort};

        let i64_sort = I64Sort.to_arcsort();
        GenericFunctionDecl {
            name: name.to_owned(),
            subtype: FunctionSubtype::Custom,
            schema: Schema::new(vec!["i64".to_owned()], "i64".to_owned()),
            resolved_schema: ResolvedCall::Func(FuncType {
                identity: CallableIdentity::Function(identity),
                name: name.to_owned(),
                subtype: FunctionSubtype::Custom,
                input: vec![i64_sort.clone()],
                outputs: vec![i64_sort],
            }),
            merge: None,
            cost: None,
            unextractable: true,
            internal_hidden: false,
            internal_let: false,
            span: Span::Panic,
            term_constructor: None,
            identity_vals: None,
            internal_term_node: false,
        }
    }

    fn function(identity: FunctionRegistrationId, backend_id: u32, name: &str) -> Function {
        Function::from_resolved_decl(
            resolved_decl(identity, name),
            false,
            egglog_bridge::FunctionId::new(backend_id),
        )
        .unwrap()
    }

    #[test]
    fn construction_uses_exact_resolved_schema_not_diagnostic_schema_strings() {
        use crate::ast::Schema;

        let identity = FunctionRegistrationId::new(5);
        let mut decl = resolved_decl(identity, "diagnostic");
        decl.schema = Schema::new(vec!["String".to_owned()], "String".to_owned());
        let ResolvedCall::Func(resolved) = &decl.resolved_schema else {
            unreachable!()
        };
        let resolved_input = resolved.input[0].clone();
        let resolved_output = resolved.outputs[0].clone();

        let function = Function::from_resolved_decl(
            decl,
            true,
            egglog_bridge::FunctionId::new(91),
        )
        .unwrap();

        assert_eq!(function.registration_id(), identity);
        assert!(std::sync::Arc::ptr_eq(
            &function.schema().input[0],
            &resolved_input
        ));
        assert!(std::sync::Arc::ptr_eq(
            &function.schema().outputs[0],
            &resolved_output
        ));
        assert!(function.can_subsume());
    }

    #[test]
    fn construction_rejects_index_authority_without_name_fallback() {
        let mut decl = resolved_decl(FunctionRegistrationId::new(5), "same-diagnostic");
        let ResolvedCall::Func(resolved) = &mut decl.resolved_schema else {
            unreachable!()
        };
        resolved.identity = CallableIdentity::Index(IndexRegistrationId::new(8));

        assert!(Function::from_resolved_decl(
            decl,
            false,
            egglog_bridge::FunctionId::new(91),
        )
        .is_err());
    }

    #[test]
    fn exact_lookup_ignores_mutated_diagnostic_name_and_equal_schema() {
        let left_id = FunctionRegistrationId::new(7);
        let right_id = FunctionRegistrationId::new(9);
        let mut registry = RuntimeFunctionRegistry::default();
        registry.insert(function(left_id, 101, "left")).unwrap();
        registry.insert(function(right_id, 207, "right")).unwrap();

        let mut resolved = match &registry.get_by_name("left").unwrap().decl.resolved_schema {
            crate::ResolvedCall::Func(function) => function.clone(),
            _ => unreachable!(),
        };
        resolved.name = "right".to_owned();

        assert_eq!(registry.require_exact(&resolved).unwrap().name(), "left");
        assert_eq!(registry.get_by_name("right").unwrap().name(), "right");
    }

    #[test]
    fn exact_index_never_falls_back_to_a_same_named_function() {
        let function_id = FunctionRegistrationId::new(3);
        let index_id = IndexRegistrationId::new(3);
        let mut registry = RuntimeFunctionRegistry::default();
        registry
            .insert(function(function_id, 55, "same-diagnostic"))
            .unwrap();

        let function = registry.get_by_name("same-diagnostic").unwrap();
        let mut index = match &function.decl.resolved_schema {
            crate::ResolvedCall::Func(function) => function.clone(),
            _ => unreachable!(),
        };
        index.identity = CallableIdentity::Index(index_id);

        assert!(matches!(
            registry.require_exact(&index),
            Err(ExactFunctionLookupError::Index(exact)) if exact == index_id
        ));
    }

    #[test]
    fn failed_insert_is_atomic_and_order_is_explicit() {
        let first = FunctionRegistrationId::new(4);
        let second = FunctionRegistrationId::new(12);
        let mut registry = RuntimeFunctionRegistry::default();
        registry.insert(function(first, 31, "z")).unwrap();

        assert_eq!(
            registry.insert(function(first, 32, "a")),
            Err(RuntimeFunctionRegistryError::DuplicateIdentity(first))
        );
        assert_eq!(
            registry.insert(function(second, 33, "z")),
            Err(RuntimeFunctionRegistryError::DuplicateName("z".to_owned()))
        );
        assert_eq!(registry.len(), 1);
        assert_eq!(registry.exact_id_for_name("z"), Some(first));
        assert_eq!(
            registry
                .iter_in_declaration_order()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            vec!["z"]
        );
    }

    #[test]
    fn clone_has_independent_indexes_and_explicit_order() {
        let first = FunctionRegistrationId::new(2);
        let second = FunctionRegistrationId::new(20);
        let mut original = RuntimeFunctionRegistry::default();
        original.insert(function(first, 71, "first")).unwrap();

        let mut cloned = original.clone();
        cloned.insert(function(second, 72, "second")).unwrap();

        assert_eq!(original.len(), 1);
        assert!(original.get_by_name("second").is_none());
        assert_eq!(cloned.len(), 2);
        assert_eq!(
            cloned
                .iter_in_declaration_order()
                .map(|(name, function)| (name.as_str(), function.registration_id()))
                .collect::<Vec<_>>(),
            vec![("first", first), ("second", second)]
        );
    }
}

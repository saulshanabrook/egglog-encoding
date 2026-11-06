use super::syntax::Form;
use egglog::ast::{ParseError, Span};
use thiserror::Error;

/// A slotted feature without a proof translation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum UnsupportedProofFeature {
    /// Substitution in a rewrite right-hand side.
    #[error("uses subst, which has no proof translation")]
    Substitution,
}

/// A source error or an unsupported feature in proof mode.
#[derive(Debug, Error)]
pub enum CompileError {
    /// Invalid source syntax or declarations.
    #[error(transparent)]
    Parse(#[from] ParseError),
    /// A source feature without a proof translation.
    #[error("{span}\n{feature}")]
    UnsupportedProofFeature {
        /// Source location of the unsupported form.
        span: Span,
        /// Feature that prevents proof generation.
        feature: UnsupportedProofFeature,
    },
}

impl From<CompileError> for egglog::Error {
    fn from(error: CompileError) -> Self {
        match error {
            CompileError::Parse(error) => error.into(),
            CompileError::UnsupportedProofFeature { span, feature } => {
                ParseError(span, feature.to_string()).into()
            }
        }
    }
}

impl UnsupportedProofFeature {
    pub(super) fn check(forms: &[(Form, Span)]) -> Result<(), CompileError> {
        fn uses_subst(form: &Form) -> bool {
            matches!(form, Form::List(items) if
                items.first() == Some(&Form::Atom("subst".into()))
                    || items.iter().any(uses_subst))
        }
        for (form, span) in forms {
            if let Ok(("rewrite", [_, rhs, ..])) = form.call()
                && uses_subst(rhs)
            {
                return Err(CompileError::UnsupportedProofFeature {
                    span: span.clone(),
                    feature: Self::Substitution,
                });
            }
        }
        Ok(())
    }
}

use egglog::ast::ParseError;
use thiserror::Error;

/// A source syntax, declaration, or lowering error.
#[derive(Debug, Error)]
pub enum CompileError {
    /// Invalid source syntax or declarations.
    #[error(transparent)]
    Parse(#[from] ParseError),
}

impl From<CompileError> for egglog::Error {
    fn from(error: CompileError) -> Self {
        match error {
            CompileError::Parse(error) => error.into(),
        }
    }
}

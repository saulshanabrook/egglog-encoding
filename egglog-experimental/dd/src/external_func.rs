use egglog_backend_trait::{ExecutionState, ExternalFunction, Value};

/// A real, invokable panic sentinel registered into the embedded `Database` by
/// `Backend::new_panic`.
#[derive(Clone)]
pub struct PanicFunc {
    message: String,
}

impl PanicFunc {
    pub fn new(message: String) -> Self {
        PanicFunc { message }
    }
}

impl ExternalFunction for PanicFunc {
    fn invoke(&self, _state: &mut ExecutionState, _args: &[Value]) -> Option<Value> {
        panic!("{}", self.message);
    }
}
